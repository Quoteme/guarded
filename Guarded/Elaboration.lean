import Guarded.Syntax
import Guarded.Typed

namespace Guarded

namespace Elaboration

def errTy (span : Span) (msg : String) : GuardedType := .error ⟨span, msg⟩

def errExpr (span : Span) (msg : String) (children : List TypedExpression := []) : TypedExpression :=
  .error span children (errTy span msg)

/-! ## Types -/

/-- Elaborate a type expression. `declared` tells which names are types. -/
partial def elabType (declared : String → Bool) : TypeSyntax → GuardedType
  | .one _ => .one
  | .zero _ => .zero
  | .name id =>
    if declared id.name then .named id.name
    else errTy id.span s!"unknown type `{id.name}`"
  | .later _ b => .later (elabType declared b)
  | .labelled _ l b => .prod [(l.name, elabType declared b)]
  | .sum _ parts => .sum (components "summand" parts)
  | .prod _ parts => .prod (components "factor" parts)
  | .missing s m => errTy s m
where
  /-- Components of sums and products must be labelled, with distinct labels. -/
  components (kind : String) (parts : Array TypeSyntax) : List (String × GuardedType) :=
    parts.toList.foldl (init := []) fun acc part =>
      match part with
      | .labelled _ l b =>
        if acc.any (·.1 == l.name) then
          acc ++ [(l.name, errTy l.span s!"duplicate label `{l.name}`")]
        else acc ++ [(l.name, elabType declared b)]
      | .missing s m => acc ++ [("_", errTy s m)]
      | p => acc ++ [("_", errTy p.span s!"every {kind} must be labelled, e.g. `(label := …)`")]

/-- Replace every definition that reaches itself without passing through a
`later` by an error: such equations have no unique solution. -/
def checkGuarded (env : TypeEnvironment) (spans : Std.HashMap String Span) : TypeEnvironment := Id.run do
  let edges (n : String) : List String := (env.get? n).map GuardedType.unguardedNames |>.getD []
  let mut out := env
  for (name, _) in env.toList do
    -- depth-first search for `name` along unguarded edges
    let mut stack := edges name
    let mut seen : List String := []
    let mut cyclic := false
    for _ in [0:env.size * env.size + 1] do
      match stack with
      | [] => break
      | n :: rest =>
        stack := rest
        if n == name then cyclic := true; break
        if !seen.contains n then
          seen := n :: seen
          stack := edges n ++ stack
    if cyclic then
      out := out.insert name <| errTy (spans.getD name default)
        s!"`{name}` is not guarded: it refers to itself without an intervening `later`, \
          so the equation has no unique solution. Write e.g. `{name} := … × (tail := later {name})`"
  return out

/-! ## Expressions -/

structure Context where
  types : TypeEnvironment
  /-- globals declared so far, with their types -/
  globals : Std.HashMap String GuardedType := {}
  locals : List (String × GuardedType) := []
  /-- checking the stage-0 branch `| 1 -> …`, where `later A ≅ 1` -/
  stageZero : Bool := false
  /-- the global being defined -/
  current : Option String := none

abbrev ElaborationM := ReaderM Context

def whnf (t : GuardedType) : ElaborationM GuardedType := return (← read).types.whnf t

def defEq (a b : GuardedType) : ElaborationM Bool := return (← read).types.defEq a b

/-- Type definitions that are sums with constructor `l`, and its payload. -/
def ctorsNamed (l : String) : ElaborationM (List (String × GuardedType)) := do
  let env := (← read).types
  return env.toList.filterMap fun (n, t) =>
    match env.whnf t with
    | .sum alts => (alts.lookup l).map (n, ·)
    | _ => none

/-- Type of the field `l` of `t`, looking through `later`
(`later` preserves products: `(later (A × B)).l = later A`). -/
partial def projTy (t : GuardedType) (l : String) : ElaborationM (Option GuardedType) := do
  match ← whnf t with
  | .later a => return (← projTy a l).map .later
  | .prod fs => return fs.lookup l
  | .error e => return some (.error e)
  | _ => return none

def mismatchMsg (expected actual : GuardedType) : ElaborationM String :=
  return s!"type mismatch: expected `{expected}`, got `{actual}`"

/-- Strip leading `later`s: `later^k t ↦ (k, t)`. -/
partial def peelLater (t : GuardedType) (k : Nat := 0) : ElaborationM (Nat × GuardedType) := do
  match ← whnf t with
  | .later a => peelLater a (k + 1)
  | t => return (k, t)

def laterN : Nat → GuardedType → GuardedType
  | 0, t => t
  | k + 1, t => .later (laterN k t)

def stageZeroHint (expected : GuardedType) : String :=
  s!"`*` has type `1`, but `{expected}` is expected. `later A` is the terminal \
    object only at stage 0, i.e. in a `| 1 -> …` branch"

mutual

partial def infer : ExpressionSyntax → ElaborationM TypedExpression
  | .ident id => do
    let ctx ← read
    if let some t := ctx.locals.lookup id.name then return .local id.span id.name t
    if ctx.current == some id.name then
      return errExpr id.span s!"`{id.name}` cannot refer to itself directly; \
        use the variable bound by the `| x -> …` branch, which is its previous approximation"
    if let some t := ctx.globals.get? id.name then return .global id.span id.name t
    inferCtor id.span id none
  | .ctor s l arg => inferCtor s l (some arg)
  | .unit s => return .unit s .one
  | .record s fields => do
    let mut out := []
    let mut bad := []
    for (l, e) in fields do
      let te ← infer e
      if out.any (·.1 == l.name) then bad := bad ++ [errExpr l.span s!"duplicate field `{l.name}`" [te]]
      else out := out ++ [(l.name, te)]
    let r := TypedExpression.record s out (.prod (out.map fun (l, e) => (l, e.ty)))
    return if bad.isEmpty then r else errExpr s "record has duplicate fields" (r :: bad)
  | .proj s b l => do
    let b ← infer b
    match ← projTy b.ty l.name with
    | some t => return .proj s b l.name t
    | none => return errExpr l.span s!"`{b.ty}` has no field `{l.name}`" [b]
  | .match s scrut alts => elabMatch s scrut alts none
  | .missing s m => return errExpr s m

/-- A constructor used without an expected type: find its sum type. -/
partial def inferCtor (s : Span) (l : Identifier) (arg : Option ExpressionSyntax) : ElaborationM TypedExpression := do
  match ← ctorsNamed l.name with
  | [(tyName, payload)] => mkInj s l arg payload (.named tyName)
  | [] =>
    let children ← arg.toList.mapM infer
    let what := if arg.isSome then "constructor" else "identifier"
    return errExpr l.span s!"unknown {what} `{l.name}`" children
  | cands =>
    let children ← arg.toList.mapM infer
    let tys := ", ".intercalate (cands.map fun c => s!"`{c.1}`")
    return errExpr l.span s!"ambiguous constructor `{l.name}`: it belongs to {tys}; \
      use it where the expected type is known" children

/-- Build `l arg : ty` where `l` has payload type `payload`. -/
partial def mkInj (s : Span) (l : Identifier) (arg : Option ExpressionSyntax) (payload ty : GuardedType) : ElaborationM TypedExpression := do
  match arg with
  | some a => return .inj s l.name (← check a payload) ty
  | none =>
    match ← whnf payload with
    | .one | .error _ => return .inj s l.name (.unit s .one) ty
    | _ => return errExpr s s!"constructor `{l.name}` expects an argument of type `{payload}`"

partial def check (e : ExpressionSyntax) (expected : GuardedType) : ElaborationM TypedExpression := do
  let ctx ← read
  let exp ← whnf expected
  if exp.isError then return ← infer e
  match e, exp with
  | .unit s, .one => return .unit s expected
  | .unit s, .later _ =>
    if ctx.stageZero then return .unit s expected
    return errExpr s (stageZeroHint expected)
  | .ident id, .sum alts =>
    if (ctx.locals.lookup id.name).isNone then
      if let some p := alts.lookup id.name then return ← mkInj id.span id none p expected
    inferAndCompare e expected
  | .ctor s l arg, .sum alts =>
    match alts.lookup l.name with
    | some p => mkInj s l (some arg) p expected
    | none =>
      let names := ", ".intercalate (alts.map fun a => s!"`{a.1}`")
      return errExpr l.span s!"`{expected}` has no constructor `{l.name}`; its constructors are {names}"
        [← infer arg]
  | .record s fields, .prod fs => checkRecord s fields fs expected
  | .match s scrut alts, _ => elabMatch s scrut alts (some expected)
  | _, _ => inferAndCompare e expected

partial def inferAndCompare (e : ExpressionSyntax) (expected : GuardedType) : ElaborationM TypedExpression := do
  let t ← infer e
  if ← defEq t.ty expected then return t
  return errExpr t.span (← mismatchMsg expected t.ty) [t]

partial def checkRecord (s : Span) (fields : Array (Identifier × ExpressionSyntax))
    (fs : List (String × GuardedType)) (expected : GuardedType) : ElaborationM TypedExpression := do
  let mut out := []
  let mut bad := []
  for (l, e) in fields do
    match fs.lookup l.name with
    | some t =>
      if out.any (·.1 == l.name) then
        bad := bad ++ [errExpr l.span s!"duplicate field `{l.name}`" [← check e t]]
      else out := out ++ [(l.name, ← check e t)]
    | none => bad := bad ++ [errExpr l.span s!"`{expected}` has no field `{l.name}`" [← infer e]]
  let missing := fs.filter fun f => !out.any (·.1 == f.1)
  let r := TypedExpression.record s out expected
  if !missing.isEmpty then
    let names := ", ".intercalate (missing.map fun f => s!"`{f.1}`")
    bad := bad ++ [errExpr s s!"missing field(s) {names} of `{expected}`"]
  return if bad.isEmpty then r else .error s (r :: bad) (bad.head!.ty)

partial def elabMatch (s : Span) (scrut : ExpressionSyntax) (alts : Array (Identifier × Option Identifier × ExpressionSyntax))
    (expected : Option GuardedType) : ElaborationM TypedExpression := do
  let scrut ← infer scrut
  let (depth, inner) ← peelLater scrut.ty
  let cases := match inner with
    | .sum cs => some cs
    | _ => none
  let mut resTy := expected
  let mut out := []
  let mut bad := []
  for (l, binder, body) in alts do
    let payload := cases.bind (·.lookup l.name)
    let bTy := laterN depth (payload.getD (errTy l.span s!"no constructor `{l.name}` here"))
    let bind := binder.map fun b => (b.name, b.span, bTy)
    let bound := binder.toList.map (·.name, bTy)
    let body ← withReader (fun c => { c with locals := bound ++ c.locals }) do
      match resTy with
      | some t => check body t
      | none => infer body
    if resTy.isNone then resTy := some body.ty
    if cases.isSome && payload.isNone then
      bad := bad ++ [errExpr l.span s!"`{scrut.ty}` has no constructor `{l.name}`"]
    else if out.any (·.1 == l.name) then
      bad := bad ++ [errExpr l.span s!"duplicate alternative `{l.name}`"]
    out := out ++ [(l.name, bind, body)]
  let ty := resTy.getD .one
  let r := TypedExpression.match s scrut out ty
  match cases with
  | none =>
    if scrut.ty.isError then return r
    return errExpr scrut.span s!"cannot match on `{scrut.ty}`, which is not a sum type" [r]
  | some cs =>
    let missing := cs.filter fun c => !out.any (·.1 == c.1)
    if !missing.isEmpty then
      let names := ", ".intercalate (missing.map fun c => s!"`{c.1}`")
      bad := bad ++ [errExpr s s!"non-exhaustive match, missing {names}"]
    return if bad.isEmpty then r else .error s (r :: bad) bad.head!.ty

end

/-! ## Declarations -/

def maxEvalDepth : Nat := 64

structure ModuleState where
  globals : Std.HashMap String GuardedType := {}
  decls : Array TypedDeclaration := #[]

/-- Elaborate the body of a global with signature `dom? → cod`. -/
def elabGlobalBody (ctx : Context) (name : Identifier) (dom? : Option GuardedType) (cod : GuardedType) (body : BodySyntax) :
    GuardedType × TypedBody :=
  let ctx := { ctx with current := some name.name }
  let run {α} (m : ElaborationM α) (c : Context := ctx) : α := m.run c
  match dom?, body with
  | none, .expr e => (cod, .expr (run (check e cod)))
  | none, .branches s bs =>
    (cod, .error (errExpr s s!"branches `| 1 -> … | y -> …` define a guarded fixed point; \
      give `{name.name}` the signature `later {cod} -> {cod}`" (bs.toList.map fun b => run (infer b.body)) :: []))
  | some dom, .expr e =>
    (errTy e.span s!"a definition with signature `{dom} -> {cod}` is given by branches \
      `| 1 -> … | y -> …`", .error [run (infer e)])
  | some dom, .branches s bs => Id.run do
    let ty := if ctx.types.defEq dom (.later cod) then cod
      else errTy name.span s!"only guarded fixed points `later Y -> Y` are definable; \
        `{dom} -> {cod}` should be `later {cod} -> {cod}`"
    let zeros := bs.filter fun b => b matches { pat := .one _, .. }
    let steps := bs.filterMap fun b => match b.pat with
      | .var x => some (x, b)
      | _ => none
    let zero := zeros[0]?.map fun b => run (check b.body cod) { ctx with stageZero := true }
    let step := steps[0]?.map fun (x, b) =>
      (x, run (check b.body cod) { ctx with locals := [(x.name, .later cod)] })
    -- everything that is not exactly one zero branch and one step branch
    let mut extra : List TypedExpression := []
    for b in bs do
      match b.pat with
      | .missing ps m => extra := extra ++ [errExpr ps m [run (infer b.body)]]
      | _ => pure ()
    for b in zeros.toList.drop 1 do
      extra := extra ++ [errExpr b.span "duplicate stage-0 branch `| 1 -> …`"]
    for (_, b) in steps.toList.drop 1 do
      extra := extra ++ [errExpr b.span "duplicate step branch; only one `| y -> …` is allowed"]
    match step with
    | none =>
      let parts := zero.toList ++ extra ++
        [errExpr s s!"missing step branch `| {name.name} -> …` describing stage n+1 \
          in terms of stage n"]
      return (ty, .error parts)
    | some (x, st) =>
      if extra.isEmpty then return (ty, .fix zero x.name x.span st)
      return (ty, .error (zero.toList ++ [st] ++ extra))

def elabDecl (types : TypeEnvironment) (st : ModuleState) : DeclarationSyntax → ModuleState
  | .type .. => st   -- handled in the first pass
  | .missing s m => { st with decls := st.decls.push (.error ⟨s, m⟩) }
  | .eval s depth e =>
    let ctx : Context := { types, globals := st.globals }
    let te := (infer e).run ctx
    let (n, te) := match depth with
      | none => (5, te)
      | some (n, ns) =>
        if n ≤ maxEvalDepth then (n, te)
        else (0, errExpr ns s!"evaluation depth is limited to {maxEvalDepth}" [te])
    { st with decls := st.decls.push (.eval s n te) }
  | .global name sig body =>
    let declared (n : String) := types.contains n
    let cod := elabType declared sig.cod
    let dom := sig.dom.map (elabType declared)
    let ctx : Context := { types, globals := st.globals }
    let (ty, tb) := elabGlobalBody ctx name dom cod body
    let ty := if st.globals.contains name.name
      then errTy name.span s!"`{name.name}` is already defined" else ty
    let sigStr := match dom with
      | some d => s!"{d} → {cod}"
      | none => cod.render
    let g : TypedGlobal := { name := name.name, span := name.span, ty, sig := sigStr, body := tb }
    { globals := st.globals.insert name.name ty, decls := st.decls.push (.global g) }

end Elaboration

open Elaboration in
/-- Elaborate a parsed module. Never fails; errors live in the result. -/
def elabModule (m : ModuleSyntax) : TypedModule := Id.run do
  -- pass 1: type definitions, which may refer to each other in any order
  let typeDecls := m.filterMap fun | .type n b => some (n, b) | _ => none
  let names := typeDecls.map (·.1.name)
  let declared (n : String) := names.contains n
  let mut env : TypeEnvironment := {}
  let mut spans : Std.HashMap String Span := {}
  let mut dupErrors : Std.HashMap Nat SourceError := {}
  for h : i in [0:typeDecls.size] do
    let (n, b) := typeDecls[i]
    if env.contains n.name then
      dupErrors := dupErrors.insert i ⟨n.span, s!"type `{n.name}` is already defined"⟩
    else
      env := env.insert n.name (elabType declared b)
      spans := spans.insert n.name n.span
  env := checkGuarded env spans
  -- pass 2: everything else, in order
  let mut st : ModuleState := {}
  let mut typeIdx := 0
  for d in m do
    match d with
    | .type n _ =>
      let t := match dupErrors.get? typeIdx with
        | some e => .error e
        | none => env.getD n.name .one
      st := { st with decls := st.decls.push (.type n.name n.span t) }
      typeIdx := typeIdx + 1
    | d => st := elabDecl env st d
  return { types := env, decls := st.decls }

end Guarded
