import Lean
import LeanTools.Common
/-!
# Elaborating spec / proof text inside the project environment

Spec and proof files carry only declarations. `leantools` prepends a fixed
header (opens, options, `namespace <crate>`) and elaborates the commands on
top of an already-loaded environment, so no re-import happens per check.
-/
open Lean Elab

namespace LeanTools

/-- Header prepended to every spec/proof text. Kept in one place so that the
orchestrator, the tests and the corpus store all agree on the context a spec
elaborates in. -/
def specHeader (ns : Name) : String :=
  "open Aeneas Aeneas.Std Result\n" ++
  "set_option Aeneas.Deprecated.progressWarning false\n" ++
  "set_option maxHeartbeats 1000000\n" ++
  "set_option maxRecDepth 2048\n" ++
  "set_option synthInstance.maxSize 1000000\n" ++
  "set_option synthInstance.maxHeartbeats 4000000\n" ++
  "set_option linter.all false\n" ++
  s!"namespace {ns}\n"

structure ElabResult where
  env : Environment
  messages : MessageLog
  commands : Array Syntax
  errors : Array String
  warnings : Array String
  /-- Constants added by the text (not present in the input environment). -/
  added : Array Name

/-- Elaborate `text` (commands only, no `import`) on top of `env`. -/
def elabCommands (env : Environment) (text : String) (fileName := "<spec>") : IO ElabResult := do
  let inputCtx := Parser.mkInputContext text fileName
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let cmdState := Command.mkState env messages {}
  let s ← IO.processCommands inputCtx parserState cmdState
  let mut errors := #[]
  let mut warnings := #[]
  for msg in s.commandState.messages.toList do
    let str ← msg.toString (includeEndPos := true)
    match msg.severity with
    | .error => errors := errors.push str
    | .warning => warnings := warnings.push str
    | .information => pure ()
  let added := s.commandState.env.constants.map₂.foldl (init := #[]) fun acc n _ =>
    if env.contains n then acc else acc.push n
  return { env := s.commandState.env, messages := s.commandState.messages,
           commands := s.commands, errors, warnings, added }

/-- Was this syntax a `theorem` declaration? -/
def isTheoremCommand (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Command.declaration &&
  stx[1].isOfKind ``Parser.Command.theorem

/-- Attribute names attached to a declaration command, by reprinting its modifiers. -/
def declAttrNames (stx : Syntax) : Array String := Id.run do
  let mods := stx[0]
  let mut out := #[]
  for a in mods.getArgs do
    if a.isOfKind ``Parser.Term.attributes || a.isOfKind ``Parser.Term.attrInstance then
      out := out.push (a.reprint.getD "").trimAscii.toString
    else
      for b in a.getArgs do
        if b.isOfKind ``Parser.Term.attributes then
          out := out.push (b.reprint.getD "").trimAscii.toString
  return out

/-- The human-readable kind of a top-level command (`theorem`, `def`, …). -/
def commandKind (stx : Syntax) : String :=
  if stx.isOfKind ``Parser.Command.declaration then
    (stx[1].getKind.toString.splitOn ".").getLast!
  else (stx.getKind.toString.splitOn ".").getLast!

end LeanTools
