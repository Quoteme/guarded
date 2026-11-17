import Guarded.Typed

/-!
# Stagewise evaluation

A closed term `e : X` denotes a family of approximations `eₙ ∈ X(n)`;
`#eval` computes `eₙ` stage by stage.

A definition `y : later Y -> Y` is computed by iteration: `y₀` is the seed
given by the `| 1 ->` branch, and `yₙ₊₁` is the step branch with the bound
variable set to `yₙ ∈ Y(n) = (later Y)(n+1)`. Each stage adds the newest
element on the outside, and `yₙ₊₁` restricts to `yₙ` by dropping it again.

Since the bound variable is a previous approximation, which is fully
computed, the step branch may `match` on it (e.g. on `y.val`). At stage 0 it
is `*`, so such definitions need a `| 1 ->` branch.
-/

namespace Guarded

/-- An element of `X(n)` for some type `X` and stage `n`. -/
inductive Value where
  | unit
  | inj (label : String) (arg : Value)
  | record (fields : List (String × Value))
  deriving Inhabited

namespace Value

partial def beq : Value → Value → Bool
  | .unit, .unit => true
  | .inj l a, .inj m b => l == m && a.beq b
  | .record xs, .record ys =>
    xs.length == ys.length && (xs.zip ys).all fun (x, y) => x.1 == y.1 && x.2.beq y.2
  | _, _ => false

instance : BEq Value := ⟨beq⟩

partial def render : Value → String
  | .unit => "*"
  | .inj l .unit => l
  | .inj l v@(.inj _ (.unit)) => s!"{l} {v.render}"
  | .inj l v@(.record _) => s!"{l} {v.render}"
  | .inj l v => s!"{l} ({v.render})"
  | .record fs => "(" ++ ", ".intercalate (fs.map fun (l, v) => s!"{l} := {v.render}") ++ ")"

instance : ToString Value := ⟨render⟩

end Value

namespace Evaluation

structure Context where
  types : TypeEnvironment
  globals : Std.HashMap String TypedGlobal
  /-- local variables with their types and values at the current stage -/
  locals : List (String × GuardedType × Value) := []
  stage : Nat

abbrev Cache := Std.HashMap (String × Nat) Value

abbrev EvaluationM := ReaderT Context (StateT Cache (Except String))

def liftE {α} (x : Except String α) : EvaluationM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-- Field `l` of a value of type `t` at stage `n`, through `later`s. -/
partial def projVal (env : TypeEnvironment) (t : GuardedType) (n : Nat) (v : Value) (l : String) : Except String Value :=
  match env.whnf t, v with
  | .later a, _ => if n == 0 then pure .unit else projVal env a (n - 1) v l
  | .prod _, .record fs => match fs.lookup l with
    | some x => pure x
    | none => throw s!"no field `{l}`"
  | _, _ => throw s!"cannot project `{l}`"

mutual

partial def eval : TypedExpression → EvaluationM Value
  | .unit .. => pure .unit
  | .local _ x _ => do
    match (← read).locals.lookup x with
    | some (_, v) => pure v
    | none => throw s!"unbound variable `{x}`"
  | .global _ g _ => do globalAt g (← read).stage
  | .inj _ l a _ => .inj l <$> eval a
  | .record _ fs _ => .record <$> fs.mapM fun (l, e) => return (l, ← eval e)
  | .proj _ b l _ => do
    let v ← eval b
    let ctx ← read
    liftE (projVal ctx.types b.ty ctx.stage v l)
  | .match _ s alts _ => do
    let v ← eval s
    let .inj l payload := v | throw s!"at stage {(← read).stage} the matched value is `*` \
      (`later A` is `1` at stage 0), so there is nothing to match on; \
      give the earlier stages with a `| 1 -> …` branch"
    let some (_, bind, body) := alts.find? (·.1 == l) | throw s!"no alternative for `{l}`"
    let bound := bind.toList.map fun (x, _, t) => (x, t, payload)
    withReader (fun c => { c with locals := bound ++ c.locals }) (eval body)
  | .error .. => throw "cannot evaluate an ill-typed term"

/-- Stage `n` of the global element `name`, memoised. -/
partial def globalAt (name : String) (n : Nat) : EvaluationM Value := do
  if let some v := (← get).get? (name, n) then return v
  let ctx ← read
  let some g := ctx.globals.get? name | throw s!"unknown global `{name}`"
  if g.ty.isError then throw s!"`{name}` is ill-typed"
  let atStage {α} (k : Nat) (locals : List (String × GuardedType × Value)) (m : EvaluationM α) : EvaluationM α :=
    withReader (fun c => { c with stage := k, locals }) m
  let v ← match g.body, n with
    | .expr e, _ => atStage n [] (eval e)
    | .fix (some z) _ _ _, 0 => atStage 0 [] (eval z)
    | .fix none x _ s, 0 => atStage 0 [(x, .later g.ty, .unit)] (eval s)
    | .fix _ x _ s, k + 1 => do
      let prev ← globalAt name k
      atStage (k + 1) [(x, .later g.ty, prev)] (eval s)
    | .error _, _ => throw s!"`{name}` is ill-formed"
  modify (·.insert (name, n) v)
  return v

end

end Evaluation

/-- Result of `#eval n e`. -/
structure EvaluationReport where
  /-- `(k, eₖ)` for `k = n, n-1, …, 0` -/
  stages : List (Nat × Value)

open Evaluation in
/-- Evaluate a closed term at stages `0 … depth`. -/
def evalStages (m : TypedModule) (e : TypedExpression) (depth : Nat) : Except String EvaluationReport := do
  let globals := m.globals
  let run (k : Nat) : StateT Cache (Except String) Value :=
    (eval e).run { types := m.types, globals, stage := k }
  let (vals, _) ← (List.range (depth + 1)).mapM run |>.run {}
  return { stages := (List.range (depth + 1)).zip vals |>.reverse }

end Guarded
