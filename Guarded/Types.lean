import Std.Data.HashMap
import Guarded.Span

/-!
# Types: objects of the topos of trees

A type `X` denotes a presheaf on `ω`: a set `X(n)` of approximations for
every stage `n` with restrictions `r_n : X(n+1) → X(n)`.

* `1(n) = {*}` and `0(n) = ∅`;
* sums and products are computed stagewise;
* `(later X)(0) = 1` and `(later X)(n+1) = X(n)`.

Named types may be (mutually) recursive provided every recursive occurrence
is under `later`; such equations have a unique solution, unfolded stage by
stage.

Errors are part of the type language: `GuardedType.error` is the type of an
ill-formed or ill-typed piece of syntax and carries the diagnostic. It is
compatible with every type, so one mistake does not cascade.
-/

namespace Guarded

/-- A diagnostic stored inside the typed AST. -/
structure SourceError where
  span : Span
  msg  : String
  deriving Inhabited, BEq, Repr

inductive GuardedType where
  | one
  | zero
  | later (body : GuardedType)
  | named (name : String)
  | sum (alts : List (String × GuardedType))
  | prod (fields : List (String × GuardedType))
  | error (info : SourceError)
  deriving Inhabited, Repr

namespace GuardedType

def isError : GuardedType → Bool
  | .error _ => true
  | _ => false

/-- All errors stored in a type. -/
partial def errors : GuardedType → List SourceError
  | .error e => [e]
  | .later t => t.errors
  | .sum xs | .prod xs => xs.flatMap (·.2.errors)
  | _ => []

/-- Render with minimal parentheses. Precedence: `+` < `×` < `later`. -/
partial def renderPrec : Nat → GuardedType → String
  | _, .one => "1"
  | _, .zero => "0"
  | _, .named n => n
  | _, .error _ => "⚠"
  | p, .later t => paren (p > 2) s!"later {t.renderPrec 3}"
  | p, .sum xs => paren (p > 0) <| " + ".intercalate (xs.map field)
  | p, .prod xs => paren (p > 1) <| " × ".intercalate (xs.map field)
where
  paren (b : Bool) (s : String) := if b then s!"({s})" else s
  field (x : String × GuardedType) := s!"({x.1} := {x.2.renderPrec 0})"

def render : GuardedType → String := renderPrec 0

instance : ToString GuardedType := ⟨render⟩

/-- Names occurring outside of any `later`. A type definition is guarded
iff it cannot reach itself along such occurrences. -/
partial def unguardedNames : GuardedType → List String
  | .named n => [n]
  | .sum xs | .prod xs => xs.flatMap (·.2.unguardedNames)
  | _ => []

end GuardedType

/-- Definitions of named types. -/
abbrev TypeEnvironment := Std.HashMap String GuardedType

namespace TypeEnvironment

/-- Unfold top-level names. Unguarded cycles are rejected before any
unfolding happens, so this terminates on checked environments; the fuel
only protects against misuse. -/
def whnf (env : TypeEnvironment) (t : GuardedType) (fuel : Nat := 1000) : GuardedType :=
  match fuel, t with
  | fuel + 1, .named n =>
    match env.get? n with
    | some body => env.whnf body fuel
    | none => .error ⟨default, s!"unknown type `{n}`"⟩
  | _, t => t

/-- Equality of types up to unfolding of names. Recursive types are compared
coinductively: a pair of names already under comparison is assumed equal. -/
partial def defEq (env : TypeEnvironment) (a b : GuardedType) (seen : List (String × String) := []) : Bool :=
  match a, b with
  | .error _, _ | _, .error _ => true
  | .named x, .named y =>
    x == y || seen.contains (x, y) ||
      env.defEq (env.whnf a) (env.whnf b) ((x, y) :: seen)
  | .named _, _ => env.defEq (env.whnf a) b seen
  | _, .named _ => env.defEq a (env.whnf b) seen
  | .one, .one | .zero, .zero => true
  | .later s, .later t => env.defEq s t seen
  | .sum xs, .sum ys | .prod xs, .prod ys =>
    xs.length == ys.length &&
      (xs.zip ys).all fun (x, y) => x.1 == y.1 && env.defEq x.2 y.2 seen
  | _, _ => false

/-- `|X(n)|`, the number of approximations at stage `n`. -/
partial def card (env : TypeEnvironment) (t : GuardedType) (n : Nat) : Nat :=
  match env.whnf t with
  | .one => 1
  | .zero => 0
  | .later t => if n == 0 then 1 else env.card t (n - 1)
  | .sum xs => xs.foldl (fun acc x => acc + env.card x.2 n) 0
  | .prod xs => xs.foldl (fun acc x => acc * env.card x.2 n) 1
  | _ => 0

end TypeEnvironment

end Guarded
