import Guarded.Lexer
import Guarded.Syntax

/-!
# Parsing

The parser is total: `parseModule` always returns a module. Wherever input
does not fit the grammar it inserts a `missing` node carrying the error
message, and recovers.

Recovery is layout based. A declaration starts with an identifier or a
`#command` in column 0; everything up to the next such token belongs to it.
A broken declaration therefore never swallows the ones after it.

Grammar (per declaration):

```
decl    ::= IDENT ':=' type                     -- type definition
          | IDENT ':' type ('->' type)? ':=' body
          | '#eval' NUMBER? expr
body    ::= expr | ('|' pat '->' expr)+
pat     ::= '1' | '*' | IDENT
type    ::= prod ('+' prod)*
prod    ::= tfactor (('×' | '*') tfactor)*
tfactor ::= '1' | '0' | IDENT | 'later' tfactor | '▷' tfactor
          | '(' IDENT ':=' type ')' | '(' type ')'
expr    ::= 'match' expr '{' alt ('|' alt)* '}'
          | IDENT postfix | postfix          -- constructor application
alt     ::= IDENT IDENT? '->' expr
postfix ::= atom ('.' IDENT)*
atom    ::= '*' | '(' ')' | '(' expr ')' | IDENT
          | '(' IDENT ':=' expr (',' IDENT ':=' expr)* ')'
```
-/

namespace Guarded

namespace Parser

structure State where
  toks : Array Token
  idx  : Nat := 0
  /-- where to report errors at the end of the declaration -/
  eofSpan : Span
  /-- an error was reported in this declaration; leftover tokens are then
  a consequence and not reported again -/
  failed : Bool := false

abbrev ParserM := StateM State

/-! ## Primitive combinators -/

def peekN (k : Nat) : ParserM Token := do
  let s ← get
  return s.toks[s.idx + k]?.getD ⟨.eof, s.eofSpan⟩

/-- Peek at the next token. -/
def peek : ParserM Token := peekN 0

/-- Peek at the kind of the next token. -/
def peekKind : ParserM TokenKind := return (← peek).kind

def advance : ParserM Token := do
  let t ← peek
  modify fun s => { s with idx := s.idx + 1 }
  return t

/-- Span from `start` to the end of the last consumed token. -/
def spanFrom (start : Span) : ParserM Span := do
  let s ← get
  match s.toks[s.idx - 1]? with
  | some t => if s.idx > 0 then return start.merge t.span else return start
  | none   => return start

/-- Consume the next token if its kind satisfies `p`. -/
def eat? (p : TokenKind → Bool) : ParserM (Option Token) := do
  let t ← peek
  if p t.kind then let _ ← advance; return some t else return none

def eatKind (k : TokenKind) : ParserM (Option Token) := eat? (· == k)

/-- Check if a token is an identifier. -/
def isIdentKind : TokenKind → Bool
  | .ident _ => true
  | _        => false

def ident? : ParserM (Option Identifier) := do
  match (← peek).kind with
  | .ident n => let t ← advance; return some ⟨n, t.span⟩
  | _        => return none

/-- Message for an unexpected token. -/
def unexpected (what : String) : ParserM (Span × String) := do
  let t ← peek
  modify fun s => { s with failed := true }
  return (t.span, s!"expected {what}, found {t.kind.describe}")

/-- Tokens that end a construct; error recovery never consumes them. -/
def isCloser : TokenKind → Bool
  | .eof | .rparen | .rbrace | .comma | .bar | .assign | .arrow => true
  | _ => false

/-- Report an error at the current token, skipping it unless it closes an
enclosing construct (so every error makes progress). -/
def recover (what : String) : ParserM (Span × String) := do
  let r ← unexpected what
  if !isCloser (← peekKind) then let _ ← advance
  return r

/-! ## Types -/

mutual

/-- Parse a type. -/
partial def parseType : ParserM TypeSyntax := do
  let first ← parseProd
  if (← peekKind) != .plus then return first
  let mut parts := #[first]
  while (← eatKind .plus).isSome do
    parts := parts.push (← parseProd)
  return .sum (first.span.merge parts.back!.span) parts

partial def parseProd : ParserM TypeSyntax := do
  let first ← parseTypeFactor
  let isTimes (k : TokenKind) := k == .times || k == .star
  if !isTimes (← peekKind) then return first
  let mut parts := #[first]
  while (← eat? isTimes).isSome do
    parts := parts.push (← parseTypeFactor)
  return .prod (first.span.merge parts.back!.span) parts

partial def parseTypeFactor : ParserM TypeSyntax := do
  let t ← peek
  match t.kind with
  | .number 1 => let _ ← advance; return .one t.span
  | .number 0 => let _ ← advance; return .zero t.span
  | .number n =>
    let _ ← advance
    return .missing t.span s!"`{n}` is not a type; the only numeric types are `0` and `1`"
  | .ident n => let _ ← advance; return .name ⟨n, t.span⟩
  | .kwLater =>
    let _ ← advance
    let body ← parseTypeFactor
    return .later (t.span.merge body.span) body
  | .lparen =>
    let _ ← advance
    if isIdentKind (← peekN 0).kind && (← peekN 1).kind == .assign then
      let some label ← ident? | unreachable!
      let _ ← advance
      let body ← parseType
      closeParen t.span (.labelled · label body)
    else
      let body ← parseType
      closeParen t.span fun _ => body
  | _ =>
    let (span, msg) ← recover "a type"
    return .missing span msg

/-- Expect `)` and build the node; a missing `)` becomes an error node
wrapping nothing. -/
partial def closeParen (start : Span) (mk : Span → TypeSyntax) : ParserM TypeSyntax := do
  if (← eatKind .rparen).isSome then
    return mk (← spanFrom start)
  let (span, msg) ← unexpected "`)`"
  return .missing (start.merge span) msg

end

/-! ## Expressions -/

def isAtomStart : TokenKind → Bool
  | .ident _ | .lparen | .star => true
  | _ => false

mutual

partial def parseExpr : ParserM ExpressionSyntax := do
  let t ← peek
  match t.kind with
  | .kwMatch =>
    let _ ← advance
    let scrut ← parseExpr
    if (← eatKind .lbrace).isNone then
      let (span, msg) ← unexpected "`{` after the scrutinee of `match`"
      return .missing (t.span.merge span) msg
    let _ ← eatKind .bar
    let mut alts := #[(← parseAlt)]
    while (← eatKind .bar).isSome do
      alts := alts.push (← parseAlt)
    if (← eatKind .rbrace).isNone then
      let (span, msg) ← unexpected "`}` closing the `match`"
      return .missing (t.span.merge span) msg
    return .match (← spanFrom t.span) scrut alts
  | .ident n =>
    if isAtomStart (← peekN 1).kind then
      let _ ← advance
      let arg ← parsePostfix
      return .ctor (t.span.merge arg.span) ⟨n, t.span⟩ arg
    parsePostfix
  | _ => parsePostfix

partial def parseAlt : ParserM (Identifier × Option Identifier × ExpressionSyntax) := do
  let start ← peek
  let some label ← ident? | do
    let (span, msg) ← recover "a constructor name"
    return (⟨"_", span⟩, none, .missing span msg)
  let binder ← ident?
  if (← eatKind .arrow).isNone then
    let (span, msg) ← unexpected "`->`"
    return (label, binder, .missing (start.span.merge span) msg)
  return (label, binder, ← parseExpr)

partial def parsePostfix : ParserM ExpressionSyntax := do
  let mut e ← parseAtom
  while (← peekKind) == .dot do
    let _ ← advance
    match ← ident? with
    | some l => e := .proj (e.span.merge l.span) e l
    | none =>
      let (span, msg) ← unexpected "a field name after `.`"
      e := .missing (e.span.merge span) msg
  return e

partial def parseAtom : ParserM ExpressionSyntax := do
  let t ← peek
  match t.kind with
  | .star => let _ ← advance; return .unit t.span
  | .ident n => let _ ← advance; return .ident ⟨n, t.span⟩
  | .lparen =>
    let _ ← advance
    if let some close ← eatKind .rparen then
      return .unit (t.span.merge close.span)
    if isIdentKind (← peekN 0).kind && (← peekN 1).kind == .assign then
      parseRecord t.span
    else
      let body ← parseExpr
      if (← eatKind .rparen).isNone then
        let (span, msg) ← unexpected "`)`"
        return .missing (t.span.merge span) msg
      return body
  | _ =>
    let (span, msg) ← recover "an expression"
    return .missing span msg

/-- Fields of a record literal, after the opening `(`. -/
partial def parseRecord (start : Span) : ParserM ExpressionSyntax := do
  let mut fields := #[]
  repeat
    let some label ← ident? | do
      let (span, msg) ← recover "a field name"
      return .missing (start.merge span) msg
    if (← eatKind .assign).isNone then
      let (span, msg) ← unexpected s!"`:=` after field `{label.name}`"
      return .missing (start.merge span) msg
    fields := fields.push (label, ← parseExpr)
    if (← eatKind .comma).isNone then break
  if (← eatKind .rparen).isNone then
    let (span, msg) ← unexpected "`,` or `)` in record"
    return .missing (start.merge span) msg
  return .record (← spanFrom start) fields

end

/-! ## Declarations -/

def parsePat : ParserM PatternSyntax := do
  let t ← peek
  match t.kind with
  | .number 1 | .star => let _ ← advance; return .one t.span
  | .ident n => let _ ← advance; return .var ⟨n, t.span⟩
  | _ =>
    let (span, msg) ← recover "`1` or a variable"
    return .missing span msg

def parseBranch : ParserM BranchSyntax := do
  let bar ← advance
  let pat ← parsePat
  if (← eatKind .arrow).isNone then
    let (span, msg) ← unexpected "`->`"
    return ⟨bar.span.merge span, pat, .missing span msg⟩
  let body ← parseExpr
  return ⟨bar.span.merge body.span, pat, body⟩

def parseBody : ParserM BodySyntax := do
  let start ← peek
  if start.kind != .bar then return .expr (← parseExpr)
  let mut bs := #[]
  while (← peekKind) == .bar do
    bs := bs.push (← parseBranch)
  return .branches (← spanFrom start.span) bs

def parseDecl : ParserM DeclarationSyntax := do
  let t ← peek
  match t.kind with
  | .cmdEval =>
    let _ ← advance
    let n ← peek
    let depth ← match n.kind with
      | .number k => do let _ ← advance; pure (some (k, n.span))
      | _ => pure none
    let e ← parseExpr
    return .eval (← spanFrom t.span) depth e
  | .cmdUnknown c =>
    let _ ← advance
    return .missing t.span s!"unknown command `#{c}`; the only command is `#eval`"
  | .ident n =>
    let _ ← advance
    let name : Identifier := ⟨n, t.span⟩
    if (← eatKind .assign).isSome then
      return .type name (← parseType)
    if (← eatKind .colon).isSome then
      let first ← parseType
      let sig ← if (← eatKind .arrow).isSome then
          pure { dom := some first, cod := ← parseType : SignatureSyntax }
        else pure { dom := none, cod := first : SignatureSyntax }
      if (← eatKind .assign).isNone then
        let (span, msg) ← unexpected "`:=`"
        return .missing (t.span.merge span) msg
      return .global name sig (← parseBody)
    let (span, msg) ← unexpected s!"`:=` (type definition) or `:` (signature) after `{n}`"
    return .missing (t.span.merge span) msg
  | _ =>
    let (span, msg) ← unexpected "a declaration `X := …`, `x : T := …` or `#eval`"
    return .missing span msg

/-- Parse one layout chunk; tokens left over become an extra error. -/
def parseChunk : ParserM (Array DeclarationSyntax) := do
  let d ← parseDecl
  let rest ← peek
  let s ← get
  if rest.kind == .eof || s.failed then return #[d]
  let last := s.toks.back?.map (·.span) |>.getD rest.span
  return #[d, .missing (rest.span.merge last) s!"unexpected {rest.kind.describe}"]

/-- A declaration begins at an identifier or command in column 0. -/
def startsDecl (t : Token) : Bool :=
  t.span.start.col == 0 &&
    match t.kind with
    | .ident _ | .cmdEval | .cmdUnknown _ => true
    | _ => false

/-- Group tokens into declarations by layout. -/
def chunks (toks : Array Token) : Array (Array Token) := Id.run do
  let mut out : Array (Array Token) := #[]
  let mut cur : Array Token := #[]
  for t in toks do
    if startsDecl t && !cur.isEmpty then
      out := out.push cur
      cur := #[]
    cur := cur.push t
  if !cur.isEmpty then out := out.push cur
  return out

end Parser

open Parser in
/-- Parse a whole `.grd` file. -/
def parseModule (src : String) : ModuleSyntax :=
  (chunks (tokenize src)).flatMap fun toks =>
    let last := toks.back!.span
    (parseChunk.run' { toks, eofSpan := ⟨last.stop, last.stop⟩ } : Array DeclarationSyntax)

end Guarded
