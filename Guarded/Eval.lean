import Guarded.Typed

/-!
# Stagewise evaluation

A closed term `e : X` denotes a global element `1 → X`, i.e. a compatible
family of approximations `eₙ ∈ X(n)`. `evalAt n e` computes `eₙ`.

* `next e` at stage 0 is `*` (since `(later X)(0) = 1`); at stage `n+1` it is
  `e` at stage `n`, with all free variables restricted along `r_n`.
* A guarded fixed point `y : later Y -> Y` is computed by iteration:
  `y₀` from the `| 1 ->` branch and `yₙ₊₁` from the step branch with the
  bound variable set to `yₙ ∈ Y(n) = (later Y)(n+1)`.

`#eval` also checks naturality, `r_n(yₙ₊₁) = yₙ`. It can only fail when the
`| 1 ->` branch disagrees with the step branch, in which case the
definition is not a morphism of the topos of trees.
-/

namespace Guarded

/-- An element of `X(n)` for some type `X` and stage `n`. Elements of
`(later X)(n+1)` are elements of `X(n)`, so `later` needs no constructor. -/
inductive Val where
  | unit
  | inj (label : String) (arg : Val)
  | record (fields : List (String × Val))
  deriving Inhabited

namespace Val

partial def beq : Val → Val → Bool
  | .unit, .unit => true
  | .inj l a, .inj m b => l == m && a.beq b
  | .record xs, .record ys =>
    xs.length == ys.length && (xs.zip ys).all fun (x, y) => x.1 == y.1 && x.2.beq y.2
  | _, _ => false

instance : BEq Val := ⟨beq⟩

partial def render : Val → String
  | .unit => "*"
  | .inj l .unit => l
  | .inj l v@(.inj _ (.unit)) => s!"{l} {v.render}"
  | .inj l v@(.record _) => s!"{l} {v.render}"
  | .inj l v => s!"{l} ({v.render})"
  | .record fs => "(" ++ ", ".intercalate (fs.map fun (l, v) => s!"{l} := {v.render}") ++ ")"

instance : ToString Val := ⟨render⟩

end Val

/-- The restriction `r_n : X(n+1) → X(n)`. -/
partial def restrict (env : TypeEnv) (t : Ty) (n : Nat) (v : Val) : Except String Val :=
  match env.whnf t, v with
  | .one, _ => pure .unit
  | .later a, _ => if n == 0 then pure .unit else restrict env a (n - 1) v
  | .sum alts, .inj l a => do
    let some p := alts.lookup l | throw s!"no constructor `{l}`"
    return .inj l (← restrict env p n a)
  | .prod fs, .record xs => .record <$> xs.mapM fun (l, a) => do
    let some p := fs.lookup l | throw s!"no field `{l}`"
    return (l, ← restrict env p n a)
  | .zero, _ => throw "the empty type has no elements"
  | t, _ => throw s!"cannot restrict a value of type `{t}`"

namespace Eval

structure Ctx where
  types : TypeEnv
  globals : Std.HashMap String TGlobal
  /-- local variables with their types and values at the current stage -/
  locals : List (String × Ty × Val) := []
  stage : Nat

abbrev Cache := Std.HashMap (String × Nat) Val

abbrev EvalM := ReaderT Ctx (StateT Cache (Except String))

def liftE {α} (x : Except String α) : EvalM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-- Field `l` of a value of type `t` at stage `n`, through `later`s. -/
partial def projVal (env : TypeEnv) (t : Ty) (n : Nat) (v : Val) (l : String) : Except String Val :=
  match env.whnf t, v with
  | .later a, _ => if n == 0 then pure .unit else projVal env a (n - 1) v l
  | .prod _, .record fs => match fs.lookup l with
    | some x => pure x
    | none => throw s!"no field `{l}`"
  | _, _ => throw s!"cannot project `{l}`"

mutual

partial def eval : TExpr → EvalM Val
  | .unit .. => pure .unit
  | .local _ x _ => do
    match (← read).locals.lookup x with
    | some (_, v) => pure v
    | none => throw s!"unbound variable `{x}`"
  | .global _ g _ => do globalAt g (← read).stage
  | .inj _ l a _ => .inj l <$> eval a
  | .record _ fs _ => .record <$> fs.mapM fun (l, e) => return (l, ← eval e)
  | .next _ b _ => do
    let ctx ← read
    match ctx.stage with
    | 0 => pure .unit
    | n + 1 =>
      let locals ← ctx.locals.mapM fun (x, t, v) => do
        return (x, t, ← liftE (restrict ctx.types t n v))
      withReader (fun c => { c with stage := n, locals }) (eval b)
  | .proj _ b l _ => do
    let v ← eval b
    let ctx ← read
    liftE (projVal ctx.types b.ty ctx.stage v l)
  | .match _ s alts _ => do
    let v ← eval s
    let .inj l payload := v | throw "match on a non-constructor value"
    let some (_, bind, body) := alts.find? (·.1 == l) | throw s!"no alternative for `{l}`"
    let bound := bind.toList.map fun (x, _, t) => (x, t, payload)
    withReader (fun c => { c with locals := bound ++ c.locals }) (eval body)
  | .error .. => throw "cannot evaluate an ill-typed term"

/-- Stage `n` of the global element `name`, memoised. -/
partial def globalAt (name : String) (n : Nat) : EvalM Val := do
  if let some v := (← get).get? (name, n) then return v
  let ctx ← read
  let some g := ctx.globals.get? name | throw s!"unknown global `{name}`"
  if g.ty.isError then throw s!"`{name}` is ill-typed"
  let atStage {α} (k : Nat) (locals : List (String × Ty × Val)) (m : EvalM α) : EvalM α :=
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

end Eval

/-- Result of `#eval n e`. -/
structure EvalReport where
  /-- `(k, eₖ)` for `k = n, n-1, …, 0` -/
  stages : List (Nat × Val)
  /-- stages `k` where `r_k(eₖ₊₁) ≠ eₖ`, with the restricted value -/
  unnatural : List (Nat × Val)

open Eval in
/-- Evaluate a closed term at stages `0 … depth`. -/
def evalStages (m : TModule) (e : TExpr) (depth : Nat) : Except String EvalReport := do
  let globals := m.globals
  let run (k : Nat) : StateT Cache (Except String) Val :=
    (eval e).run { types := m.types, globals, stage := k }
  let (vals, _) ← (List.range (depth + 1)).mapM run |>.run {}
  let mut unnatural := []
  for (k, (v, v')) in (List.range depth).zip (vals.zip (vals.drop 1)) do
    let r ← restrict m.types e.ty k v'
    if !(r == v) then unnatural := unnatural ++ [(k, r)]
  return { stages := (List.range (depth + 1)).zip vals |>.reverse, unnatural }

end Guarded
