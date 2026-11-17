import Guarded.Span

/-!
# Surface syntax

The untyped AST produced by the parser. Parse errors are not exceptions:
they are `missing` nodes that carry their message and location, and the
elaborator turns them into error types (`Ty.error`) in the typed AST.
-/

namespace Guarded

structure Ident where
  name : String
  span : Span
  deriving Inhabited, Repr

instance : HasSpan Ident := ⟨Ident.span⟩

/-- Type expressions. -/
inductive TypeSyn where
  | one (span : Span)
  | zero (span : Span)
  | name (id : Ident)
  | later (span : Span) (body : TypeSyn)
  /-- `(label := T)`: a component of a sum or a product -/
  | labelled (span : Span) (label : Ident) (body : TypeSyn)
  | sum (span : Span) (parts : Array TypeSyn)
  | prod (span : Span) (parts : Array TypeSyn)
  | missing (span : Span) (msg : String)
  deriving Inhabited, Repr

def TypeSyn.span : TypeSyn → Span
  | .one s | .zero s | .later s _ | .labelled s _ _ | .sum s _ | .prod s _
  | .missing s _ => s
  | .name id => id.span

instance : HasSpan TypeSyn := ⟨TypeSyn.span⟩

/-- Expressions denote (stagewise families of) values. -/
inductive ExprSyn where
  /-- a variable, a global, or a constructor without argument -/
  | ident (id : Ident)
  /-- constructor application `label arg` -/
  | ctor (span : Span) (label : Ident) (arg : ExprSyn)
  /-- `*` or `()`: the element of `1` -/
  | unit (span : Span)
  /-- `(l₁ := e₁, …, lₙ := eₙ)` -/
  | record (span : Span) (fields : Array (Ident × ExprSyn))
  /-- `next e : later A` for `e : A` -/
  | next (span : Span) (body : ExprSyn)
  /-- `e.label` -/
  | proj (span : Span) (body : ExprSyn) (label : Ident)
  /-- `match e { l₁ x -> e₁ | l₂ -> e₂ }` -/
  | «match» (span : Span) (scrutinee : ExprSyn) (alts : Array (Ident × Option Ident × ExprSyn))
  | missing (span : Span) (msg : String)
  deriving Inhabited, Repr

def ExprSyn.span : ExprSyn → Span
  | .ident id => id.span
  | .ctor s _ _ | .unit s | .record s _ | .next s _ | .proj s _ _ | .match s _ _
  | .missing s _ => s

instance : HasSpan ExprSyn := ⟨ExprSyn.span⟩

/-- Signature of a global: `T` or `D -> T`. -/
structure SigSyn where
  dom : Option TypeSyn
  cod : TypeSyn
  deriving Inhabited, Repr

/-- Left-hand side of a branch `| pat -> e`. -/
inductive PatSyn where
  /-- `1` (or `*`): the stage-0 case, where `later Y` is the terminal object -/
  | one (span : Span)
  /-- `y`: binds the previous approximation `y : later Y` -/
  | var (id : Ident)
  | missing (span : Span) (msg : String)
  deriving Inhabited, Repr

def PatSyn.span : PatSyn → Span
  | .one s | .missing s _ => s
  | .var id => id.span

structure BranchSyn where
  span : Span
  pat  : PatSyn
  body : ExprSyn
  deriving Inhabited, Repr

inductive BodySyn where
  | expr (e : ExprSyn)
  | branches (span : Span) (bs : Array BranchSyn)
  deriving Inhabited, Repr

inductive DeclSyn where
  /-- `X := T` -/
  | type (name : Ident) (body : TypeSyn)
  /-- `x : S := body` -/
  | global (name : Ident) (sig : SigSyn) (body : BodySyn)
  /-- `#eval n e` -/
  | eval (span : Span) (depth : Option (Nat × Span)) (e : ExprSyn)
  | missing (span : Span) (msg : String)
  deriving Inhabited, Repr

abbrev Module := Array DeclSyn

end Guarded
