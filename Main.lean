import Guarded

/-!
`guarded`            — run the language server on stdin/stdout
`guarded check FILE` — print the diagnostics of FILE (including `#eval` output)
-/

open Guarded

def severityLabel : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .info => "info"

def check (path : System.FilePath) : IO UInt32 := do
  let a := analyze (← IO.FS.readFile path)
  for d in a.diags do
    IO.println s!"{path}:{d.span.start}: {severityLabel d.severity}: {d.msg}"
  return if a.diags.any (·.severity == .error) then 1 else 0

def main : List String → IO UInt32
  | ["check", path] => check path
  | [] => do Server.run; return 0
  | _ => do
    IO.eprintln "usage: guarded            (language server on stdio)\n       guarded check FILE"
    return 2
