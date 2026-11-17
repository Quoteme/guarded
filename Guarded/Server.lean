import Lapis
import Guarded.Analysis

/-!
# Language server

Glue between the analysis pipeline and the lapis LSP framework. The server
keeps the latest `Analysis` of every open document; diagnostics (including
the output of `#eval`) are republished on open and on every change.
-/

namespace Guarded.Server

open Lapis.Protocol.Types
open Lapis.Protocol.Messages
open Lapis.Protocol.Capabilities
open Lapis.Concurrent.LspActor
open Lapis.Concurrent.Dispatcher
open Lapis.Transport
open Lapis.Protocol.JsonRpc

structure State where
  docs : Std.HashMap DocumentUri Analysis := {}

abbrev Handler (α : Type) := RequestContext State → α → IO Unit

def toPosition (p : Pos) : Position := { line := p.line, character := p.col }

def fromPosition (p : Position) : Pos := ⟨p.line, p.character⟩

def toRange (s : Span) : Range := { start := toPosition s.start, «end» := toPosition s.stop }

def toSeverity : Severity → DiagnosticSeverity
  | .error => .error
  | .warning => .warning
  | .info => .information

def toDiagnostic (d : Diag) : Diagnostic :=
  { range := toRange d.span
    severity := some (toSeverity d.severity)
    source := some "guarded"
    message := d.msg }

/-- Re-analyse `text` and publish its diagnostics. -/
def refresh (ctx : RequestContext State) (uri : DocumentUri) (version : Option Int)
    (text : String) : IO Unit := do
  let a := analyze text
  ctx.modifyUserState fun s => { s with docs := s.docs.insert uri a }
  ctx.publishDiagnostics { uri, version, diagnostics := a.diags.map toDiagnostic }

def onOpen : Handler DidOpenTextDocumentParams := fun ctx p =>
  refresh ctx p.textDocument.uri (some p.textDocument.version) p.textDocument.text

/-- With full synchronisation the last change carries the whole text. -/
def onChange : Handler DidChangeTextDocumentParams := fun ctx p => do
  let some change := p.contentChanges.back? | return
  refresh ctx p.textDocument.uri (some p.textDocument.version) change.text

def onClose : Handler DidCloseTextDocumentParams := fun ctx p => do
  ctx.modifyUserState fun s => { s with docs := s.docs.erase p.textDocument.uri }
  ctx.publishDiagnostics { uri := p.textDocument.uri, diagnostics := #[] }

def onHover (ctx : RequestContext State) (p : HoverParams) : IO (Option Hover) := do
  let some a := (← ctx.getUserState).docs.get? p.textDocument.uri | return none
  let some (span, text) := a.hover? (fromPosition p.position) | return none
  return some { contents := { kind := .markdown, value := text }, range := some (toRange span) }

def config : LspConfig State :=
  LspConfig.new "guarded"
    |>.withVersion "0.1.0"
    |>.withCapabilities {
      textDocumentSync := some {
        openClose := some true
        change := some .full
      }
      hoverProvider := some true
    }
    |>.onNotification "textDocument/didOpen" onOpen
    |>.onNotification "textDocument/didChange" onChange
    |>.onNotification "textDocument/didClose" onClose
    |>.onRequestOpt "textDocument/hover" onHover

/-- Stdio transport that terminates the process on `exit` or end of input.
(lapis' own shutdown waits for its actors and does not return.) Exit code 0
iff `shutdown` was requested first, as the LSP specification asks. -/
structure ExitingTransport where
  inner : Lapis.Transport.Stdio.StdioTransport
  shutdownRequested : IO.Ref Bool

instance : Transport ExitingTransport where
  readMessage t := do
    let msg ← Transport.readMessage t.inner
    match msg with
    | some (.request r) =>
      if r.method == "shutdown" then t.shutdownRequested.set true
      return msg
    | some (.notification n) =>
      if n.method != "exit" then return msg
      IO.Process.exit (if ← t.shutdownRequested.get then 0 else 1)
    | none => IO.Process.exit (if ← t.shutdownRequested.get then 0 else 1)
    | _ => return msg
  writeMessage t := Transport.writeMessage t.inner
  close t := Transport.close t.inner

def run : IO Unit := do
  let t : ExitingTransport := { inner := ← Lapis.Transport.Stdio.create, shutdownRequested := ← IO.mkRef false }
  runServer t config {}

end Guarded.Server
