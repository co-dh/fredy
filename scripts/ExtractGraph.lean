/- Extract the declaration graph of the Fredy library.
   Run from repo root:  lake env lean --run scripts/ExtractGraph.lean
   Output: graph/decls.tsv  (name  kind  file  line  type  doc-first-line)
           graph/deps.tsv   (src  dst)
   Names have the ubiquitous `Freyd.` prefix stripped (8794/8802 decls carry it); the
   only root-level names left as-is are the `Cat` typeclass fields and the tool `main`.
   Edges are true proof-level dependencies (constants of the elaborated type + proof term,
   the same data `#print axioms` walks), not import-level or syntactic references.
   Orphan modules (not imported by the root `Fredy`) are loaded each in its own
   environment — two orphans may define the same constant name, so they cannot
   share one environment. Core-only: reads the already-built .olean files. -/
import Lean
open Lean

def kindOf : ConstantInfo → Option String
  | .thmInfo _    => some "thm"
  | .defnInfo _   => some "def"
  | .axiomInfo _  => some "axiom"
  | .inductInfo _ => some "ind"
  | .opaqueInfo _ => some "opaque"
  | _             => none   -- ctors/recursors are folded into their inductive below

def modToPath (m : Name) (ext : String) : System.FilePath :=
  System.FilePath.mk (m.toString.replace "." "/" ++ "." ++ ext)

/-- All module names under dir (source of truth = .lean files, so orphans count too). -/
partial def collectMods (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in (← dir.readDir) do
    if (← e.path.isDir) then
      out := out ++ (← collectMods e.path (pre.str e.fileName))
    else if e.path.extension == some "lean" then
      out := out.push (pre.str (e.path.fileStem.getD ""))
  return out

/-- Drop the ubiquitous `Freyd.` namespace prefix so graph node names read short.
    Both endpoints of every edge and every decl name go through this, keeping the two
    files join-consistent. `Cat.*` and `main` don't start with `Freyd.`, so they're untouched. -/
def shortName (n : Name) : String :=
  let s := n.toString
  if s.take 6 == "Freyd." then (s.drop 6).toString else s

abbrev Row := Name × String × Name × Nat            -- name, kind, module, line

def oneLine (s : String) : String := Id.run do
  let mut out := ""
  let mut sp := false
  for c in s.toList do
    if c == ' ' || c == '\t' || c == '\n' then sp := true
    else
      if sp && !out.isEmpty then out := out.push ' '
      out := out.push c
      sp := false
  return out

/-- Pretty-printed type and first docstring line for each row (needs a MetaM run).
    Strip the ubiquitous `Freyd.` prefix from the printed type and doc text (same reason
    `shortName` strips it from the decl/edge names) so the whole tsv reads prefix-free. These
    columns are display-only, so a blunt substring strip is fine and also catches names the
    pretty-printer leaves fully qualified (inaccessible `✝` auxiliaries) and literal docstrings. -/
def annotate (env : Environment) (rows : Array Row) : IO (Array (Row × String × String)) := do
  let ctx : Core.Context := { fileName := "<extract>", fileMap := default }
  let go : CoreM _ := rows.mapM fun row@(n, _, _, _) => do
    let ci := (env.find? n).get!
    let ty ← try
        pure ((oneLine (toString (← Meta.MetaM.run' (Meta.ppExpr ci.type)))).replace "Freyd." "")
      catch _ => pure ""
    let doc := (((← findDocString? env n).getD "").splitOn "\n" |>.headD "").replace "Freyd." ""
    return (row, ty, oneLine doc)
  Prod.fst <$> go.toIO ctx { env }

/-- Rows and edges for the declarations of `env` living in modules satisfying `wanted`. -/
def extract (env : Environment) (wanted : Name → Bool) :
    Array Row × Array (Name × Name) := Id.run do
  let fredyMod? (n : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if `Fredy |>.isPrefixOf m then some m else none
  -- pass 1: user-written declarations in Fredy modules (targets for edges)
  let mut kept : Std.HashMap Name (String × Name × Nat) := {}
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail then continue
    let some kind := kindOf ci | continue
    -- `instance` declarations are `.defnInfo` too (kindOf → "def"); relabel via the
    -- instance-attribute environment extension so they're distinguishable in the graph.
    let kind := if kind == "def" && Meta.isInstanceCore env n then "instance" else kind
    let some m := fredyMod? n | continue
    -- compiler-generated helpers (injEq, noConfusion, …) carry no declaration range
    let some r := declRangeExt.find? env n | continue
    kept := kept.insert n (kind, m, r.range.pos.line)
  -- pass 2: rows for wanted modules; edges routed through generated/internal constants
  let mut rows := #[]
  let mut edges := #[]
  for (src, ci) in env.constants.toList do
    let some (kind, m, line) := kept.get? src | continue
    unless wanted m do continue
    rows := rows.push (src, kind, m, line)
    let raw := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    let mut stack := raw.toList
    let mut visited : Std.HashSet Name := {}
    while true do
      match stack with
      | [] => break
      | n :: rest =>
        stack := rest
        if visited.contains n || n == src then continue
        visited := visited.insert n
        if kept.contains n then
          edges := edges.push (src, n)
        else if let some ci' := env.find? n then
          match ci' with
          | .ctorInfo _ | .recInfo _ => stack := n.getPrefix :: stack
          | _ =>
            -- expand aux constants (match_, proof_, eq lemmas, …) but only inside Fredy
            if (fredyMod? n).isSome then
              stack := (ci'.type.getUsedConstants
                ++ (ci'.value?.map (·.getUsedConstants)).getD #[]).toList ++ stack
  return (rows, edges)

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let all ← collectMods "Fredy" `Fredy
  let mut built := #[]
  let mut skipped := #[]
  for m in all do
    if (← (".lake/build/lib/lean" / modToPath m "olean").pathExists)
    then built := built.push m else skipped := skipped.push m
  unless skipped.isEmpty do
    IO.eprintln s!"warning: {skipped.size} modules have no .olean (run lake build): {skipped.toList}"
  -- root closure first, then every orphan in its own environment
  -- loadExts := true: without it, environment-extension state (incl. the instance
  -- registry `Meta.instanceExtension` used by `isInstanceCore` in `extract`) is left unloaded.
  let envRoot ← importModules #[{ module := `Fredy }] {} (trustLevel := 1024) (loadExts := true)
  let mut done : Std.HashSet Name :=
    .ofArray (envRoot.header.moduleNames.filter (`Fredy |>.isPrefixOf ·))
  let (rows₀, edges₀) := extract envRoot done.contains
  let mut rows ← annotate envRoot rows₀
  let mut edges := edges₀
  let mut orphans := 0
  for m in built do
    if done.contains m then continue
    orphans := orphans + 1
    let env ← importModules #[{ module := m }] {} (trustLevel := 1024) (loadExts := true)
    let mods := env.header.moduleNames.filter fun x =>
      (`Fredy |>.isPrefixOf x) && !done.contains x
    let fresh : Std.HashSet Name := .ofArray mods
    let (r, e) := extract env fresh.contains
    rows := rows ++ (← annotate env r)
    edges := edges ++ e
    done := mods.foldl (·.insert ·) done
  IO.FS.createDirAll "graph"
  let sorted := (rows.map fun ((n, k, m, l), ty, doc) =>
      ((modToPath m "lean").toString, l, shortName n, k, ty, doc))
    |>.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  IO.FS.withFile "graph/decls.tsv" .write fun h => do
    for (f, l, n, k, ty, doc) in sorted do
      h.putStrLn s!"{n}\t{k}\t{f}\t{l}\t{ty}\t{doc}"
  let es := (edges.map fun (s, t) => s!"{shortName s}\t{shortName t}") |>.qsort (· < ·) |>.toList.eraseReps.toArray
  IO.FS.withFile "graph/deps.tsv" .write fun h => do
    for e in es do h.putStrLn e
  IO.println s!"{sorted.size} declarations, {es.size} edges ({done.size} modules, {orphans} orphan roots)"
