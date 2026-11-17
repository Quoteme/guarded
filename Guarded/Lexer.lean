import Guarded.Span

/-!
# Tokenization

The lexer is total: every character of the input ends up in some token.
Characters that do not belong to the language become `TokenKind.unknown`
tokens, which the parser later turns into error nodes.

Comments start with `--` or `//` and run to the end of the line.
-/

namespace Guarded

inductive TokenKind where
  | ident (name : String)
  | number (n : Nat)
  /-- `later` or `▷` -/
  | kwLater
  | kwNext
  | kwMatch
  /-- `#eval` -/
  | cmdEval
  /-- `#foo` for any other `foo` -/
  | cmdUnknown (name : String)
  /-- `:=` -/
  | assign
  | colon
  | lparen | rparen
  | lbrace | rbrace
  | plus
  /-- `×` -/
  | times
  /-- `*`: the unit value, or ASCII product in types -/
  | star
  /-- `->` or `→` -/
  | arrow
  | bar
  | comma
  | dot
  | unknown (c : Char)
  | eof
  deriving Inhabited, BEq, Repr

namespace TokenKind

def describe : TokenKind → String
  | .ident n      => s!"identifier `{n}`"
  | .number n     => s!"number `{n}`"
  | .kwLater      => "`later`"
  | .kwNext       => "`next`"
  | .kwMatch      => "`match`"
  | .cmdEval      => "`#eval`"
  | .cmdUnknown n => s!"`#{n}`"
  | .assign       => "`:=`"
  | .colon        => "`:`"
  | .lparen       => "`(`"
  | .rparen       => "`)`"
  | .lbrace       => "`{`"
  | .rbrace       => "`}`"
  | .plus         => "`+`"
  | .times        => "`×`"
  | .star         => "`*`"
  | .arrow        => "`->`"
  | .bar          => "`|`"
  | .comma        => "`,`"
  | .dot          => "`.`"
  | .unknown c    => s!"unexpected character `{c}`"
  | .eof          => "end of declaration"

end TokenKind

structure Token where
  kind : TokenKind
  span : Span
  deriving Inhabited, Repr

instance : HasSpan Token := ⟨Token.span⟩

/-! ## Character classes -/

private def isSymbolChar (c : Char) : Bool :=
  c == '×' || c == '→' || c == '▷'

def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || (c.val > 127 && !isSymbolChar c)

def isIdentChar (c : Char) : Bool :=
  isIdentStart c || c.isDigit || c == '\''

private def keyword? : String → Option TokenKind
  | "later" => some .kwLater
  | "next"  => some .kwNext
  | "match" => some .kwMatch
  | _       => none

/-! ## The lexer

A small cursor over the input characters, tracking line and column. -/

private structure Cursor where
  chars : Array Char
  idx   : Nat := 0
  pos   : Pos := ⟨0, 0⟩

private abbrev LexM := StateM Cursor

private def peekAt (k : Nat) : LexM (Option Char) :=
  return (← get).chars[(← get).idx + k]?

private def bump : LexM Unit := modify fun c =>
  match c.chars[c.idx]? with
  | some '\n' => { c with idx := c.idx + 1, pos := ⟨c.pos.line + 1, 0⟩ }
  | some _    => { c with idx := c.idx + 1, pos := { c.pos with col := c.pos.col + 1 } }
  | none      => c

/-- Consume characters while `p` holds and return them. -/
private partial def takeWhile (p : Char → Bool) (acc : String := "") : LexM String := do
  match ← peekAt 0 with
  | some c => if p c then bump; takeWhile p (acc.push c) else return acc
  | none   => return acc

private partial def skipTrivia : LexM Unit := do
  match ← peekAt 0, ← peekAt 1 with
  | some '-', some '-' | some '/', some '/' =>
    let _ ← takeWhile (· != '\n'); skipTrivia
  | some c, _ =>
    if c.isWhitespace then bump; skipTrivia
  | none, _ => pure ()

/-- Read one token; `none` at end of input. -/
private def nextToken : LexM (Option Token) := do
  skipTrivia
  let start := (← get).pos
  let some c ← peekAt 0 | return none
  let c1 ← peekAt 1
  let single (k : TokenKind) : LexM TokenKind := do bump; return k
  let double (k : TokenKind) : LexM TokenKind := do bump; bump; return k
  let kind ← match c, c1 with
    | ':', some '=' => double .assign
    | '-', some '>' => double .arrow
    | ':', _ => single .colon
    | '(', _ => single .lparen
    | ')', _ => single .rparen
    | '{', _ => single .lbrace
    | '}', _ => single .rbrace
    | '+', _ => single .plus
    | '×', _ => single .times
    | '*', _ => single .star
    | '→', _ => single .arrow
    | '▷', _ => single .kwLater
    | '|', _ => single .bar
    | ',', _ => single .comma
    | '.', _ => single .dot
    | '#', _ => do
        bump
        let name ← takeWhile isIdentChar
        pure (if name == "eval" then .cmdEval else .cmdUnknown name)
    | _, _ =>
      if c.isDigit then do
        let digits ← takeWhile Char.isDigit
        pure (.number digits.toNat!)
      else if isIdentStart c then do
        let name ← takeWhile isIdentChar
        pure ((keyword? name).getD (.ident name))
      else single (.unknown c)
  return some ⟨kind, ⟨start, (← get).pos⟩⟩

private partial def lexAll (acc : Array Token) : LexM (Array Token) := do
  match ← nextToken with
  | some t => lexAll (acc.push t)
  | none   => return acc

/-- Split source text into tokens. Never fails. -/
def tokenize (src : String) : Array Token :=
  (lexAll #[]).run' { chars := src.toList.toArray }

end Guarded
