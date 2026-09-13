import LeanTools.Common
import LeanTools.Frontend
import LeanTools.Mutate
/-!
# `leantools embedtext` — canonical definition text for embeddings

The unit's source (all members) with doc comments removed and every
identifier that does not resolve to a global constant (binders, `let`-bound
names, pattern variables, loop-state names) renamed to `x0, x1, …` in order
of first appearance; constants and field projections are kept.
-/
open Lean Elab

namespace LeanTools.EmbedText

/-- Does `id` (as written) resolve to a constant under the spec header's opens? -/
def resolves (env : Environment) (ns : Name) (id : Name) : Bool :=
  let opens : List OpenDecl := [.simple `Aeneas [], .simple `Aeneas.Std [], .simple `Aeneas.Std.Result [],
                                .simple `Aeneas.Std.ControlFlow [], .simple `Aeneas.Std.Error [], .simple ns []]
  !(ResolveName.resolveGlobalName env {} ns opens id).isEmpty

/-- Strip doc comments (`/-- … -/`) and line comments. -/
def stripComments (s : String) : String := Id.run do
  let mut out := ""
  let mut i := 0
  let cs := s.toList.toArray
  while i < cs.size do
    if i + 1 < cs.size && cs[i]! == '/' && cs[i+1]! == '-' then
      let mut j := i + 2
      while j + 1 < cs.size && !(cs[j]! == '-' && cs[j+1]! == '/') do j := j + 1
      i := j + 2
    else if i + 1 < cs.size && cs[i]! == '-' && cs[i+1]! == '-' then
      while i < cs.size && cs[i]! != '\n' do i := i + 1
    else
      out := out.push cs[i]!
      i := i + 1
  return out

/-- Identifier occurrences (start, end, name) in a syntax tree. -/
partial def identOccurrences (stx : Syntax) (acc : Array (String.Pos.Raw × String.Pos.Raw × Name)) :
    Array (String.Pos.Raw × String.Pos.Raw × Name) :=
  match stx with
  | .ident info _ n _ =>
    -- only identifiers written in the source (not produced by macro expansion)
    match info.getPos? (canonicalOnly := true), info.getTailPos? (canonicalOnly := true) with
    | some s, some e => if s.byteIdx < e.byteIdx then acc.push (s, e, n) else acc
    | _, _ => acc
  | .node _ _ args => args.foldl (fun a c => identOccurrences c a) acc
  | _ => acc

/-- Drop attribute lines (`@[…]`): noise for embeddings, and their names are not constants. -/
def stripAttributes (s : String) : String :=
  String.intercalate "\n" ((s.splitOn "\n").filter fun l => !(l.trimAscii.toString.startsWith "@["))

def canonicalize (env : Environment) (ns : Name) (keep : Std.HashSet String) (src : String) : IO String := do
  let text := stripAttributes (stripComments src)
  -- parse through the frontend on a copy named apart so the originals do not clash
  let header := Mutate.mutantHeader ns
  let r ← elabCommands env (header ++ text) "<embed>"
  -- collect ident occurrences (position, name) inside the parsed commands
  let mut occ : Array (String.Pos.Raw × String.Pos.Raw × Name) := #[]
  for c in r.commands do occ := identOccurrences c occ
  let full := header ++ text
  let sorted := occ.qsort fun a b => a.1.byteIdx < b.1.byteIdx
  let mut table : Std.HashMap String String := {}
  let mut edits : Array Mutate.Edit := #[]
  let mut counter := 0
  for (s, e, n) in sorted do
    if s.byteIdx < header.rawEndPos.byteIdx then continue
    -- head component decides: `self.len` → rename `self` only
    let head : Name := match n.components with
      | c :: _ => c
      | [] => n
    if keep.contains n.toString || resolves env ns n || resolves env ns head then continue
    let headStr := head.toString
    let newHead ← match table[headStr]? with
      | some v => pure v
      | none =>
        let v := s!"x{counter}"
        counter := counter + 1
        table := table.insert headStr v
        pure v
    let rest := String.ofList (n.toString.toList.drop headStr.length)
    edits := edits.push { startPos := s, endPos := e, replacement := newHead ++ rest }
  let out := Mutate.applyEdits full edits
  return (String.Pos.Raw.extract out header.rawEndPos out.rawEndPos).trimAscii.toString

def run (p : Project) (unit : Name) (members? : Option (Array Name)) : IO Json := do
  let env ← p.loadEnv
  let mods := crateModules env p.ns
  let members := members?.getD (loopFamily env mods unit)
  let lineOf (m : Name) : Nat := match declRangeExt.find? env m with
    | some r => r.range.pos.line
    | none => 0
  let members := members.qsort fun a b => lineOf a < lineOf b
  let mut cache : SourceCache := {}
  let mut src := ""
  for m in members do
    let (c', s?) ← declSource p env cache m
    cache := c'
    src := src ++ (s?.getD "") ++ "\n\n"
  -- rename the members themselves apart (they already exist in the environment)
  let nsPrefix := p.ns.toString ++ "."
  let short (n : Name) : String :=
    let s := n.toString
    if s.startsWith nsPrefix then String.ofList (s.toList.drop nsPrefix.length) else s
  let mut tbl : Std.HashMap String String := {}
  for m in members do
    tbl := tbl.insert (short m) (short m ++ "_emb") |>.insert (nsPrefix ++ short m) (nsPrefix ++ short m ++ "_emb")
  let renamed := Mutate.renameIdents src tbl
  let keep : Std.HashSet String := tbl.fold (fun acc _ v => acc.insert v) {}
  let canon ← canonicalize env p.ns keep renamed
  -- undo the `_emb` suffix in the output
  let text := canon.replace "_emb" ""
  return Json.mkObj [("unit", toJson unit.toString), ("text", toJson text), ("source", toJson src.trimAscii.toString)]

end LeanTools.EmbedText
