import Guarded.Span

/-!
# Surface syntax

The untyped AST produced by the parser. Parse errors are not exceptions:
they are `missing` nodes that carry their message and location, and the
elaborator turns them into error types (`GuardedType.error`) in the typed AST.
-/

namespace Guarded

structure Identifier where
  name : String
  span : Span
  deriving Inhabited, Repr

instance : HasSpan Identifier := ⟨Identifier.span⟩

/-- Type expressions. -/
inductive TypeSyntax where
  | one (span : Span)
  | zero (span : Span)
  | name (id : Identifier)
  | later (span : Span) (body : TypeSyntax)
  /-- `(label := T)`: a component of a sum or a product -/
  | labelled (span : Span) (label : Identifier) (body : TypeSyntax)
  | sum (span : Span) (parts : Array TypeSyntax)
  | prod (span : Span) (parts : Array TypeSyntax)
  | missing (span : Span) (msg : String)
  deriving Inhabited, Repr

def TypeSyntax.span : TypeSyntax → Span
  | .one s | .zero s | .later s _ | .labelled s _ _ | .sum s _ | .prod s _
  | .missing s _ => s
  | .name id => id.span

instance : HasSpan TypeSyntax := ⟨TypeSyntax.span⟩

/-- Expressions denote (stagewise families of) values. -/
inductive ExpressionSyntax where
  /-- a variable, a global, or a constructor without argument -/
  | ident (id : Identifier)
  /-- constructor application `label arg` -/
  | ctor (span : Span) (label : Identifier) (arg : ExpressionSyntax)
  /-- `*` or `()`: the element of `1` -/
  | unit (span : Span)
  /-- `(l₁ := e₁, …, lₙ := eₙ)` -/
  | record (span : Span) (fields : Array (Identifier × ExpressionSyntax))
  /-- `e.label` -/
  | proj (span : Span) (body : ExpressionSyntax) (label : Identifier)
  /-- `match e { l₁ x -> e₁ | l₂ -> e₂ }` -/
  | «match» (span : Span) (scrutinee : ExpressionSyntax) (alts : Array (Identifier × Option Identifier × ExpressionSyntax))
  | missing (span : Span) (msg : String)
  deriving Inhabited, Repr

def ExpressionSyntax.span : ExpressionSyntax → Span
  | .ident id => id.span
  | .ctor s _ _ | .unit s | .record s _ | .proj s _ _ | .match s _ _
  | .missing s _ => s

instance : HasSpan ExpressionSyntax := ⟨ExpressionSyntax.span⟩

/-- Signature of a global: `T` or `D -> T`. -/
structure SignatureSyntax where
  dom : Option TypeSyntax
  cod : TypeSyntax
  deriving Inhabited, Repr

/-- Left-hand side of a branch `| pat -> e`. -/
inductive PatternSyntax where
  /-- `1` (or `*`): the stage-0 case, where `later Y` is the terminal object -/
  | one (span : Span)
  /-- `y`: binds the previous approximation `y : later Y` -/
  | var (id : Identifier)
  | missing (span : Span) (msg : String)
  deriving Inhabited, Repr

def PatternSyntax.span : PatternSyntax → Span
  | .one s | .missing s _ => s
  | .var id => id.span

structure BranchSyntax where
  span : Span
  pat  : PatternSyntax
  body : ExpressionSyntax
  deriving Inhabited, Repr

inductive BodySyntax where
  | expr (e : ExpressionSyntax)
  | branches (span : Span) (bs : Array BranchSyntax)
  deriving Inhabited, Repr

inductive DeclarationSyntax where
  /-- `X := T` -/
  | type (name : Identifier) (body : TypeSyntax)
  /-- `x : S := body` -/
  | global (name : Identifier) (sig : SignatureSyntax) (body : BodySyntax)
  /-- `#eval n e` -/
  | eval (span : Span) (depth : Option (Nat × Span)) (e : ExpressionSyntax)
  | missing (span : Span) (msg : String)
  deriving Inhabited, Repr

abbrev ModuleSyntax := Array DeclarationSyntax

end Guarded
