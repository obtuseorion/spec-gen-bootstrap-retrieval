import LeanTools.Common
import LeanTools.Graph
import LeanTools.SpecForm
import LeanTools.Mutate
import LeanTools.Gate
import LeanTools.ProofCheck
import LeanTools.EmbedText
/-!
`lake exe leantools <cmd> --project <root> [--namespace Corpus] <cmd args…>`

Every command prints exactly one JSON object on stdout. Failures print
`{"error": "…"}` and exit 1. Nothing here is meant for humans to parse.
-/
open Lean LeanTools

def usage : String :=
  "usage: leantools <graph|specform|gate|proofcheck|embedtext> --project <root> [--namespace NS] [args]"

unsafe def main (argv : List String) : IO UInt32 := do
  Lean.enableInitializersExecution
  try
    match argv with
    | [] => emitError usage; return (1 : UInt32)
    | cmd :: rest =>
      let args := parseArgs rest
      let p ← Project.ofArgs args
      let out ← match cmd with
        | "graph" => Graph.run p
        | "specform" => do
          let some unit := args["unit"]? | throw <| IO.userError "missing --unit"
          let some spec := args["spec"]? | throw <| IO.userError "missing --spec"
          let members := args["members"]?.map fun s => (s.splitOn ",").toArray.map String.toName
          SpecForm.run p unit.toName members spec
        | "mutate" => do
          let some unit := args["unit"]? | throw <| IO.userError "missing --unit"
          let members := args["members"]?.map fun s => (s.splitOn ",").toArray.map String.toName
          let max := (args["max-mutants"]?.bind String.toNat?).getD 200
          let seed := (args["seed"]?.bind String.toNat?).getD 0
          Mutate.run p unit.toName members max seed
        | "gate" => do
          let some unit := args["unit"]? | throw <| IO.userError "missing --unit"
          let some spec := args["spec"]? | throw <| IO.userError "missing --spec"
          let members := args["members"]?.map fun s => (s.splitOn ",").toArray.map String.toName
          let runs := (args["runs"]?.bind String.toNat?).getD 200
          let max := (args["max-mutants"]?.bind String.toNat?).getD 200
          let timeout := (args["timeout"]?.bind String.toNat?).getD 10
          let seed := (args["seed"]?.bind String.toNat?).getD 0
          let chunk := (args["chunk"]?.bind String.toNat?).getD 16
          Gate.run p unit.toName members spec runs max timeout seed chunk
        | "proofcheck" => do
          let some unit := args["unit"]? | throw <| IO.userError "missing --unit"
          let some spec := args["spec"]? | throw <| IO.userError "missing --spec"
          let some proof := args["proof"]? | throw <| IO.userError "missing --proof"
          let callee := args.getD "callee-specs" "."
          let members := args["members"]?.map fun s => (s.splitOn ",").toArray.map String.toName
          let typesModule := args["types-module"]?.map String.toName
          ProofCheck.run p unit.toName members spec proof callee typesModule
        | "embedtext" => do
          let some unit := args["unit"]? | throw <| IO.userError "missing --unit"
          let members := args["members"]?.map fun s => (s.splitOn ",").toArray.map String.toName
          EmbedText.run p unit.toName members
        | other => throw <| IO.userError s!"unknown command {other}\n{usage}"
      emit out
      -- Runaway evaluation tasks (mutants that diverge) would keep the runtime from
      -- shutting down; the JSON is complete at this point, so leave immediately.
      (← IO.getStdout).flush
      IO.Process.exit 0
  catch e =>
    emitError (toString e)
    return (1 : UInt32)
