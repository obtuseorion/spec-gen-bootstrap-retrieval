import LeanTools.Common
/-!
# `leantools graph` — dependency graph, units, processing order (Task 1)

Nodes are Aeneas-emitted functions (definitions returning `Result _`).
Edges follow `getUsedConstants`, walking through Lean-generated auxiliaries.
`_loop` helpers are attached to their parent by name pattern *and* by edge;
strongly connected components become `scc` units; the output order is
reverse topological (callees first), ties broken by module then name.
-/
open Lean Meta

namespace LeanTools.Graph

structure Signature where
  arg_type_heads : Array String
  ret_type_head : String
  called_consts : Array String
  has_loop : Bool
  deriving ToJson, FromJson, Repr

structure Unit where
  id : String
  kind : String
  members : Array String
  loops : Array String
  callees : Array String
  externals : Array String            -- crate constants without a value (external models) reached by the unit
  is_divergent : Bool
  is_generic : Bool
  signature : Signature
  source : String
  module : String
  deriving ToJson, FromJson, Repr

/-- Per-constant facts gathered from the environment. -/
structure NodeInfo where
  name : Name
  module : Name
  reach : Std.HashSet Name          -- constants reached from the value (see `reachableConsts`)
  divergent : Bool
  generic : Bool
  argHeads : Array String
  retHead : String
  deriving Inhabited

/-- Type parameters (`{T : Type}`), instance-implicit binders, or trait-instance
binders (`(OrdInst : avl.Ord T)`) make a unit generic. -/
private def isGenericType (mods : Std.HashSet Name) (type : Expr) : MetaM Bool :=
  forallTelescope type fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      let t ← instantiateMVars d.type
      if d.binderInfo == .instImplicit then return true
      if (← whnfD t).isSort then return true
      if let some h := t.getAppFn.constName? then
        if isCrateConst (← getEnv) mods h && (d.userName.toString.endsWith "Inst") then return true
    return false

private def typeHead (t : Expr) : String :=
  match t.getAppFn with
  | .const n _ => shortName n
  | .forallE .. => "→"
  | .sort .. => "Type"
  | _ => "?"

private def argAndRetHeads (type : Expr) : MetaM (Array String × String) :=
  forallTelescope type fun xs body => do
    let mut heads := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo == .default then
        heads := heads.push (typeHead (← instantiateMVars d.type))
    let ret := match body.getAppFn.constName?, body.getAppArgs with
      | some `Aeneas.Std.Result, #[a] => s!"Result {typeHead a}"
      | some n, _ => shortName n
      | none, _ => "?"
    return (heads, ret)

/-- Tarjan's SCC over an adjacency map (iterative). -/
private partial def tarjan (nodes : Array Name) (adj : Std.HashMap Name (Array Name)) : Array (Array Name) := Id.run do
  let mut index : Std.HashMap Name Nat := {}
  let mut low : Std.HashMap Name Nat := {}
  let mut onStack : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  let mut counter := 0
  let mut comps : Array (Array Name) := #[]
  for root in nodes do
    if index.contains root then continue
    let mut frames : Array (Name × Nat) := #[(root, 0)]
    index := index.insert root counter; low := low.insert root counter; counter := counter + 1
    stack := stack.push root; onStack := onStack.insert root
    while !frames.isEmpty do
      let (v, i) := frames.back!
      let ns := adj.getD v #[]
      if i < ns.size then
        frames := frames.pop.push (v, i + 1)
        let w := ns[i]!
        if !index.contains w then
          index := index.insert w counter; low := low.insert w counter; counter := counter + 1
          stack := stack.push w; onStack := onStack.insert w
          frames := frames.push (w, 0)
        else if onStack.contains w then
          low := low.insert v (min (low.getD v 0) (index.getD w 0))
      else
        frames := frames.pop
        if let some (u, _) := frames.back? then
          low := low.insert u (min (low.getD u 0) (low.getD v 0))
        if low.getD v 0 == index.getD v 0 then
          let mut comp : Array Name := #[]
          while true do
            let w := stack.back!
            stack := stack.pop; onStack := onStack.erase w
            comp := comp.push w
            if w == v then break
          comps := comps.push comp
  return comps

/-- Phase timing to stderr (stdout stays pure JSON). -/
def tick (label : String) (t0 : Nat) : IO Nat := do
  let t ← IO.monoMsNow
  IO.eprintln s!"[graph] {label}: {t - t0} ms"
  return t

def run (p : Project) : IO Json := do
  let t ← IO.monoMsNow
  let env ← p.loadEnv
  let t ← tick "loadEnv" t
  let mods := crateModules env p.ns
  let modName (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  -- 1. nodes
  let (nodes, _, _) ← runMeta env do
    let mut acc : Array Name := #[]
    for n in crateConstNames env mods do
      if let some ci := env.find? n then
        if ← isEmittedFunction env mods n ci then acc := acc.push n
    return acc.qsort Name.lt
  let t ← tick "nodes" t
  let nodeSet : Std.HashSet Name := nodes.foldl (·.insert ·) {}
  let isNode := fun n => nodeSet.contains n
  -- 2. per-node facts
  let (infos, _, _) ← runMeta env do
    let mut m : Std.HashMap Name NodeInfo := {}
    for n in nodes do
      let ci := env.find? n |>.get!
      let reach := reachableConsts env mods isNode n
      let (argHeads, retHead) ← argAndRetHeads ci.type
      let generic ← isGenericType mods ci.type
      m := m.insert n { name := n, module := modName n, reach,
                        divergent := reach.contains ``Lean.Order.fix,
                        generic, argHeads, retHead }
    -- `mutual … partial_fixpoint` blocks: every member's value references one packed
    -- `<first>.mutual` constant and the recursive calls go through the fixpoint tuple,
    -- not through constants. Make the members reach each other so they form an SCC.
    let mut groups : Std.HashMap Name (Array Name) := {}
    for n in nodes do
      let ci := env.find? n |>.get!
      for u in ci.value!.getUsedConstants do
        if let .str _ "mutual" := u then
          groups := groups.insert u ((groups.getD u #[]).push n)
    for (_, members) in groups.toList do
      if members.size > 1 then
        for n in members do
          let info := m.get! n
          m := m.insert n { info with reach := members.foldl (·.insert ·) info.reach }
    return m
  let t ← tick "infos" t
  -- 3. loop attachment: by name, then verified by edge (reachability inside the
  -- whole name-based family, so nested loops `f_loop0_loop0` reached through
  -- `f_loop0.body` are attached too).
  let mut parentOf : Std.HashMap Name Name := {}
  let mut warnings : Array String := #[]
  let rootByName (n : Name) : Name := loopRootByName isNode n
  let mut groups : Std.HashMap Name (Array Name) := {}
  for n in nodes do
    let r := rootByName n
    if r != n then groups := groups.insert r ((groups.getD r #[]).push n)
  for (root, kids) in groups.toList do
    let fam : Std.HashSet Name := kids.foldl (·.insert ·) (({} : Std.HashSet Name).insert root)
    let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert root
    let mut queue : List Name := [root]
    while true do
      match queue with
      | [] => break
      | v :: rest =>
        queue := rest
        for u in (infos.get! v).reach.toList do
          if fam.contains u && !seen.contains u then
            seen := seen.insert u; queue := u :: queue
    for k in kids do
      if seen.contains k then
        let p := (loopParentByName isNode k).getD root
        parentOf := parentOf.insert k (if seen.contains p then p else root)
      else warnings := warnings.push s!"{k}: name suggests a loop of {root} but no edge reaches it; treated as its own unit"
  -- root of the loop-parent chain (loops nest: f_loop0_loop0 → f_loop0 → f)
  let famOf (n : Name) : Name := Id.run do
    let mut cur := n
    for _ in [0:16] do
      match parentOf[cur]? with
      | some p => cur := p
      | none => break
    return cur
  let t ← tick "loops" t
  -- 4. family-level graph (contract loops into parents)
  let families : Array Name := nodes.filter fun n => !parentOf.contains n
  let mut adj : Std.HashMap Name (Array Name) := {}
  for f in families do
    let members := nodes.filter fun n => famOf n == f
    let mut targets : Std.HashSet Name := {}
    for m in members do
      for u in (infos.get! m).reach.toList do
        if isNode u then
          let g := famOf u
          if g != f then targets := targets.insert g
    adj := adj.insert f (targets.toArray.qsort Name.lt)
  let t ← tick "families" t
  -- 5. SCCs and processing order (Kahn over the condensation, ready set sorted by module, name)
  let comps := tarjan families adj
  let compId (c : Array Name) : Name := (c.qsort Name.lt)[0]!
  let mut compOf : Std.HashMap Name Name := {}
  for c in comps do
    let cid := compId c
    for m in c do compOf := compOf.insert m cid
  -- callee component → set of caller components; indeg(caller) = number of distinct callee components
  let mut callersOf : Std.HashMap Name (Std.HashSet Name) := {}
  let mut indeg : Std.HashMap Name Nat := {}
  for c in comps do
    let cid := compId c
    indeg := indeg.insertIfNew cid 0
    for m in c do
      for t in adj.getD m #[] do
        let tc := compOf.get! t
        if tc != cid then
          let s := callersOf.getD tc {}
          if !s.contains cid then
            callersOf := callersOf.insert tc (s.insert cid)
            indeg := indeg.insert cid (indeg.getD cid 0 + 1)
  let t ← tick "condensation" t
  -- precomputed sort keys; `ready` is kept sorted by insertion
  let mut keyOf : Std.HashMap Name String := {}
  for c in comps do
    let cid := compId c
    keyOf := keyOf.insert cid s!"{modName cid}|{cid}"
  let key (cid : Name) : String := keyOf.getD cid cid.toString
  let insertSorted (arr : Array Name) (x : Name) : Array Name := Id.run do
    let kx := key x
    let mut i := 0
    while i < arr.size && key arr[i]! < kx do i := i + 1
    return arr.insertIdx! i x
  let mut ready : Array Name := ((comps.map compId).filter (fun c => indeg.getD c 0 == 0)).qsort (fun a b => key a < key b)
  let mut order : Array Name := #[]
  while !ready.isEmpty do
    let c := ready[0]!
    ready := ready.eraseIdx! 0
    order := order.push c
    for caller in (callersOf.getD c {}).toList do
      let d := indeg.getD caller 0 - 1
      indeg := indeg.insert caller d
      if d == 0 then ready := insertSorted ready caller
  if order.size != comps.size then
    warnings := warnings.push s!"order covers {order.size} of {comps.size} components"
  let t ← tick "order" t
  -- 6. units
  let mut cache : SourceCache := {}
  let mut units : Array Unit := #[]
  let compMembers : Std.HashMap Name (Array Name) := comps.foldl (init := {}) fun m c => m.insert (compId c) c
  for cid in order do
    let fams := (compMembers.get! cid).qsort Name.lt
    let loops := (nodes.filter fun n => parentOf.contains n && fams.contains (famOf n)).qsort Name.lt
    let all := fams ++ loops
    let mut callees : Std.HashSet Name := {}
    let mut called : Std.HashSet Name := {}
    let mut externals : Std.HashSet Name := {}
    let mut src := ""
    let mut divergent := false
    let mut generic := false
    for m in all do
      let info := infos.get! m
      divergent := divergent || info.divergent
      generic := generic || info.generic
      for u in info.reach.toList do
        if isNode u then
          let c := compOf.get! (famOf u)
          if c != cid then callees := callees.insert c
        else if isCrateConst env mods u then
          match env.find? u with
          | some (.axiomInfo _) | some (.opaqueInfo _) => externals := externals.insert u
          | _ => pure ()
        else if (`Aeneas.Std).isPrefixOf u && !(u.getString!.startsWith "inst") then
          if let some ci := env.find? u then
            if (ci.isDefinition || ci.isTheorem) && !(ci.type.getForallBody.isSort) then
              called := called.insert u
      let (c', s?) ← declSource p env cache m
      cache := c'
      src := src ++ (s?.getD s!"-- <source of {m} unavailable>") ++ "\n\n"
    let primary := infos.get! fams[0]!
    if units.size == 0 then let _ ← tick "first unit" t
    units := units.push {
      id := cid.toString
      kind := if fams.size > 1 then "scc" else "def"
      members := fams.map toString
      loops := loops.map toString
      callees := (callees.toArray.map toString).qsort (· < ·)
      externals := (externals.toArray.map toString).qsort (· < ·)
      is_divergent := divergent
      is_generic := generic
      signature := {
        arg_type_heads := primary.argHeads
        ret_type_head := primary.retHead
        called_consts := (called.toArray.map toString).qsort (· < ·)
        has_loop := !loops.isEmpty }
      source := (src.trimAsciiEnd).toString
      module := (modName fams[0]!).toString }
  let _ ← tick "units" t
  return Json.mkObj [
    ("units", toJson units),
    ("order", toJson (order.map toString)),
    ("warnings", toJson warnings),
    ("node_count", toJson nodes.size) ]

end LeanTools.Graph
