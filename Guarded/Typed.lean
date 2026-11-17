import Guarded.Types

/-!
# Typed AST

Output of elaboration. Every expression node records its type. Ill-formed
or ill-typed nodes have type `GuardedType.error`, which carries the diagnostic;
`TypedModule.errors` collects them. There is no separate error channel.
-/

namespace Guarded

inductive TypedExpression where
  | local (span : Span) (name : String) (ty : GuardedType)
  | global (span : Span) (name : String) (ty : GuardedType)
  /-- `*`; its type is `1`, or `later A` at stage 0 -/
  | unit (span : Span) (ty : GuardedType)
  | inj (span : Span) (label : String) (arg : TypedExpression) (ty : GuardedType)
  | record (span : Span) (fields : List (String × TypedExpression)) (ty : GuardedType)
  | proj (span : Span) (body : TypedExpression) (label : String) (ty : GuardedType)
  /-- alternatives: label, binder `(name, span, type)`, body -/
  | «match» (span : Span) (scrutinee : TypedExpression)
      (alts : List (String × Option (String × Span × GuardedType) × TypedExpression)) (ty : GuardedType)
  /-- an erroneous node; `ty` is a `GuardedType.error`. Well-formed parts of the
  input are kept as children (for hover and further diagnostics). -/
  | error (span : Span) (children : List TypedExpression) (ty : GuardedType)
  deriving Inhabited

namespace TypedExpression

def ty : TypedExpression → GuardedType
  | .local _ _ t | .global _ _ t | .unit _ t | .inj _ _ _ t | .record _ _ t
  | .proj _ _ _ t | .match _ _ _ t | .error _ _ t => t

def span : TypedExpression → Span
  | .local s _ _ | .global s _ _ | .unit s _ | .inj s _ _ _ | .record s _ _
  | .proj s _ _ _ | .match s _ _ _ | .error s _ _ => s

def children : TypedExpression → List TypedExpression
  | .inj _ _ a _ | .proj _ a _ _ => [a]
  | .record _ fs _ => fs.map (·.2)
  | .match _ s alts _ => s :: alts.map (·.2.2)
  | .error _ cs _ => cs
  | _ => []

/-- All errors in the tree, outermost first. -/
partial def errors (e : TypedExpression) : List SourceError :=
  e.ty.errors ++ (match e with
    | .match _ _ alts _ => alts.flatMap fun (_, b, _) => b.elim [] (·.2.2.errors)
    | _ => []) ++ e.children.flatMap errors

/-- Global names the expression depends on. -/
partial def globals (e : TypedExpression) : List String :=
  (match e with | .global _ n _ => [n] | _ => []) ++ e.children.flatMap globals

/-- Innermost node whose span contains `p`. Children with the same span as
their parent (the implicit `*` of a bare constructor `l`) are skipped. -/
partial def nodeAt? (e : TypedExpression) (p : Pos) : Option TypedExpression :=
  if !e.span.contains p then none
  else
    let inner := e.children.filter (!·.span == e.span)
    (inner.findSome? (·.nodeAt? p)).getD e |> some

end TypedExpression

instance : HasSpan TypedExpression := ⟨TypedExpression.span⟩

/-- Body of a global element. -/
inductive TypedBody where
  /-- `x : Y := e` -/
  | expr (e : TypedExpression)
  /-- `y : later Y -> Y := | 1 -> seed | prev -> step`, defined by iteration:
  stage 0 is `seed` (or `step` with `prev := *` if absent), stage `n+1` is
  `step` with `prev` bound to stage `n`. -/
  | fix (zero : Option TypedExpression) (prev : String) (prevSpan : Span) (step : TypedExpression)
  /-- ill-formed body; the error is the global's type or inside `parts` -/
  | error (parts : List TypedExpression)
  deriving Inhabited

def TypedBody.exprs : TypedBody → List TypedExpression
  | .expr e => [e]
  | .fix z _ _ s => z.toList ++ [s]
  | .error ps => ps

structure TypedGlobal where
  name : String
  span : Span
  /-- the type `Y` of which this is a global element `1 → Y` -/
  ty   : GuardedType
  /-- signature as written, for display -/
  sig  : String
  body : TypedBody
  deriving Inhabited

inductive TypedDeclaration where
  | type (name : String) (span : Span) (ty : GuardedType)
  | global (g : TypedGlobal)
  | eval (span : Span) (depth : Nat) (e : TypedExpression)
  | error (info : SourceError)
  deriving Inhabited

namespace TypedDeclaration

def errors : TypedDeclaration → List SourceError
  | .type _ _ t => t.errors
  | .global g => g.ty.errors ++ g.body.exprs.flatMap (·.errors)
  | .eval _ _ e => e.errors
  | .error e => [e]

def exprs : TypedDeclaration → List TypedExpression
  | .global g => g.body.exprs
  | .eval _ _ e => [e]
  | _ => []

end TypedDeclaration

structure TypedModule where
  types : TypeEnvironment
  decls : Array TypedDeclaration
  deriving Inhabited

namespace TypedModule

/-- Every error in the module, each reported once. -/
def errors (m : TypedModule) : List SourceError :=
  (m.decls.toList.flatMap (·.errors)).foldl
    (fun acc e => if acc.contains e then acc else acc ++ [e]) []

def globals (m : TypedModule) : Std.HashMap String TypedGlobal :=
  m.decls.foldl (init := {}) fun acc d =>
    match d with
    | .global g => acc.insert g.name g
    | _ => acc

end TypedModule

end Guarded
