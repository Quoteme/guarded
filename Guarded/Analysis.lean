import Guarded.Parser
import Guarded.Elaboration
import Guarded.Evaluation

/-!
# Document analysis

The pipeline `tokenize → parse → elaborate → evaluate`, packaged for the
language server (and the command-line checker). Independent of any LSP
library.
-/

namespace Guarded

inductive Severity where
  | error | warning | info
  deriving Inhabited, BEq, Repr

structure Diagnostic where
  span : Span
  severity : Severity
  msg : String
  deriving Inhabited, Repr

structure Analysis where
  module : TypedModule
  diags : Array Diagnostic
  deriving Inhabited

/-- `| 5 -> …` lines, latest stage first. -/
def EvaluationReport.render (r : EvaluationReport) : String :=
  "\n".intercalate (r.stages.map fun (k, v) => s!"| {k} -> {v}")

def evalDiags (m : TypedModule) : TypedDeclaration → List Diagnostic
  | .eval s depth e =>
    if !e.errors.isEmpty then [] else
    match evalStages m e depth with
    | .error msg => [⟨s, .warning, s!"cannot evaluate: {msg}"⟩]
    | .ok r => [⟨s, .info, r.render⟩]
  | _ => []

/-- Analyse a document. -/
def analyze (src : String) : Analysis :=
  let m := elaborateModule (parseModule src)
  let errs := m.errors.toArray.map fun e => (⟨e.span, .error, e.msg⟩ : Diagnostic)
  { module := m, diags := errs ++ (m.decls.toList.flatMap (evalDiags m)).toArray }

/-! ## Hover -/

def cardinalities (env : TypeEnvironment) (t : GuardedType) (stages : Nat := 4) : String :=
  if t.isError then "" else
  let name := match t with
    | .named n => n
    | t => s!"({t})"
  let cs := (List.range stages).map fun n => s!"|{name}({n})| = {env.card t n}"
  "\n\n" ++ ", ".intercalate cs ++ ", …"

def describeExpr (e : TypedExpression) : String :=
  match e.ty with
  | .error info => s!"⚠ {info.msg}"
  | t =>
    let name := match e with
      | .local _ x _ => s!"{x} "
      | .global _ x _ => s!"{x} "
      | .inj s l a _ => if a.span == s then s!"{l} " else s!"{l} … "
      | _ => ""
    s!"```\n{name}: {t}\n```"

/-- Markdown hover text for position `p`, if anything is there. -/
def Analysis.hover? (a : Analysis) (p : Pos) : Option (Span × String) :=
  let env := a.module.types
  a.module.decls.toList.findSome? fun
    | .type n s t =>
      if s.contains p then some (s, s!"```\n{n} := {t}\n```" ++ cardinalities env (.named n))
      else none
    | d@(.global g) =>
      if g.span.contains p then
        some (g.span, s!"```\n{g.name} : {g.sig}\n```\nglobal element `1 → {g.ty}`" ++
          cardinalities env g.ty)
      else exprHover d
    | d => exprHover d
where
  exprHover (d : TypedDeclaration) : Option (Span × String) :=
    d.exprs.findSome? fun e => (e.nodeAt? p).map fun n => (n.span, describeExpr n)

end Guarded
