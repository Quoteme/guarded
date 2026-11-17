import Guarded.Types

/-!
# Typed AST

Output of elaboration. Every expression node records its type. Ill-formed
or ill-typed nodes have type `Ty.error`, which carries the diagnostic;
`TModule.errors` collects them. There is no separate error channel.
-/

namespace Guarded

inductive TExpr where
  | local (span : Span) (name : String) (ty : Ty)
  | global (span : Span) (name : String) (ty : Ty)
  /-- `*`; its type is `1`, or `later A` at stage 0 -/
  | unit (span : Span) (ty : Ty)
  | inj (span : Span) (label : String) (arg : TExpr) (ty : Ty)
  | record (span : Span) (fields : List (String × TExpr)) (ty : Ty)
  | proj (span : Span) (body : TExpr) (label : String) (ty : Ty)
  /-- alternatives: label, binder `(name, span, type)`, body -/
  | «match» (span : Span) (scrutinee : TExpr)
      (alts : List (String × Option (String × Span × Ty) × TExpr)) (ty : Ty)
  /-- an erroneous node; `ty` is a `Ty.error`. Well-formed parts of the
  input are kept as children (for hover and further diagnostics). -/
  | error (span : Span) (children : List TExpr) (ty : Ty)
  deriving Inhabited

namespace TExpr

def ty : TExpr → Ty
  | .local _ _ t | .global _ _ t | .unit _ t | .inj _ _ _ t | .record _ _ t
  | .proj _ _ _ t | .match _ _ _ t | .error _ _ t => t

def span : TExpr → Span
  | .local s _ _ | .global s _ _ | .unit s _ | .inj s _ _ _ | .record s _ _
  | .proj s _ _ _ | .match s _ _ _ | .error s _ _ => s

def children : TExpr → List TExpr
  | .inj _ _ a _ | .proj _ a _ _ => [a]
  | .record _ fs _ => fs.map (·.2)
  | .match _ s alts _ => s :: alts.map (·.2.2)
  | .error _ cs _ => cs
  | _ => []

/-- All errors in the tree, outermost first. -/
partial def errors (e : TExpr) : List ErrInfo :=
  e.ty.errors ++ (match e with
    | .match _ _ alts _ => alts.flatMap fun (_, b, _) => b.elim [] (·.2.2.errors)
    | _ => []) ++ e.children.flatMap errors

/-- Global names the expression depends on. -/
partial def globals (e : TExpr) : List String :=
  (match e with | .global _ n _ => [n] | _ => []) ++ e.children.flatMap globals

/-- Innermost node whose span contains `p`. Children with the same span as
their parent (the implicit `*` of a bare constructor `l`) are skipped. -/
partial def nodeAt? (e : TExpr) (p : Pos) : Option TExpr :=
  if !e.span.contains p then none
  else
    let inner := e.children.filter (!·.span == e.span)
    (inner.findSome? (·.nodeAt? p)).getD e |> some

end TExpr

instance : HasSpan TExpr := ⟨TExpr.span⟩

/-- Body of a global element. -/
inductive TBody where
  /-- `x : Y := e` -/
  | expr (e : TExpr)
  /-- `y : later Y -> Y := | 1 -> seed | prev -> step`, defined by iteration:
  stage 0 is `seed` (or `step` with `prev := *` if absent), stage `n+1` is
  `step` with `prev` bound to stage `n`. -/
  | fix (zero : Option TExpr) (prev : String) (prevSpan : Span) (step : TExpr)
  /-- ill-formed body; the error is the global's type or inside `parts` -/
  | error (parts : List TExpr)
  deriving Inhabited

def TBody.exprs : TBody → List TExpr
  | .expr e => [e]
  | .fix z _ _ s => z.toList ++ [s]
  | .error ps => ps

structure TGlobal where
  name : String
  span : Span
  /-- the type `Y` of which this is a global element `1 → Y` -/
  ty   : Ty
  /-- signature as written, for display -/
  sig  : String
  body : TBody
  deriving Inhabited

inductive TDecl where
  | type (name : String) (span : Span) (ty : Ty)
  | global (g : TGlobal)
  | eval (span : Span) (depth : Nat) (e : TExpr)
  | error (info : ErrInfo)
  deriving Inhabited

namespace TDecl

def errors : TDecl → List ErrInfo
  | .type _ _ t => t.errors
  | .global g => g.ty.errors ++ g.body.exprs.flatMap (·.errors)
  | .eval _ _ e => e.errors
  | .error e => [e]

def exprs : TDecl → List TExpr
  | .global g => g.body.exprs
  | .eval _ _ e => [e]
  | _ => []

end TDecl

structure TModule where
  types : TypeEnv
  decls : Array TDecl
  deriving Inhabited

namespace TModule

/-- Every error in the module, each reported once. -/
def errors (m : TModule) : List ErrInfo :=
  (m.decls.toList.flatMap (·.errors)).foldl
    (fun acc e => if acc.contains e then acc else acc ++ [e]) []

def globals (m : TModule) : Std.HashMap String TGlobal :=
  m.decls.foldl (init := {}) fun acc d =>
    match d with
    | .global g => acc.insert g.name g
    | _ => acc

end TModule

end Guarded
