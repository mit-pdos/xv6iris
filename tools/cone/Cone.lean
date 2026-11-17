/-
tools/cone/Cone.lean — THE STATEMENT CONE of a theorem (mini plan rev 4 §0, K5): every declaration reached from the
theorem's TYPE through definition bodies and inductive constructors (never through a theorem's proof), with its
module, start line and line count.  What a reader must vet to trust the statement; Lean checks the proofs.

  lake env lean --run tools/cone/Cone.lean <Module> <Decl> [<Decl> …]

Output, per decl: `CONE <decl> lines=<n> mini=<n>` then one `  <module> <name> <line> <lines>` per declaration
(ordered by module, then line); declarations outside `Weak.Mini` are listed by name (their lines are reported but not
counted in `mini=`).  `ALIEN <module> <name>` marks a declaration outside the allowlist (Weak.Mini, Lean core: Init,
Lean, Std; iris-lean: Iris; its lake dependencies: Batteries, Qq).
-/
import Lean
open Lean Meta

def coneOf (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut fuel := 1000000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut ns := ci.type.getUsedConstants.toList
        match ci with
        | .defnInfo d => ns := ns ++ d.value.getUsedConstants.toList
        | .inductInfo i => ns := ns ++ i.ctors
        | _ => pure ()
        todo := ns ++ todo
  return seen

def allowed (m : Name) : Bool :=
  [`Weak.Mini, `Init, `Lean, `Std, `Iris, `Batteries, `Qq].any (fun p => p.isPrefixOf m)

def report (root : Name) : CoreM Unit := do
  let env ← getEnv
  unless env.contains root do
    IO.println s!"MISSING {root}"; return
  let mut rows : Array (Name × Nat × Name × Nat) := #[]
  for n in (coneOf env [root]).toList do
    if n.isInternal then continue
    -- Generated declarations live inside their inductive's source range: count the inductive once.
    if isAuxRecursor env n || isNoConfusion env n then continue
    match env.find? n with
    | some (.ctorInfo _) | some (.recInfo _) => continue
    | _ => pure ()
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    let (line, lines) ← match ← findDeclarationRanges? n with
      | some r => pure (r.range.pos.line, r.range.endPos.line - r.range.pos.line + 1)
      | none => pure (0, 0)
    rows := rows.push (m, line, n, lines)
  rows := rows.qsort (fun a b => a.1.toString < b.1.toString || (a.1 == b.1 && a.2.1 < b.2.1))
  let tot := rows.foldl (fun s r => s + r.2.2.2) 0
  let mini := rows.foldl (fun s r => if (`Weak.Mini).isPrefixOf r.1 then s + r.2.2.2 else s) 0
  IO.println s!"CONE {root} lines={tot} mini={mini} decls={rows.size}"
  for (m, line, n, lines) in rows do
    IO.println s!"  {m} {n} {line} {lines}"
    unless allowed m do IO.println s!"ALIEN {m} {n}"

def main (args : List String) : IO Unit := do
  match args with
  | modName :: decls =>
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := modName.toName }] {} (trustLevel := 1024)
    let ctx : Core.Context := { fileName := "<cone>", fileMap := default }
    let st : Core.State := { env }
    for d in decls do
      discard <| (report d.toName).toIO ctx st
  | _ => IO.println "usage: lake env lean --run tools/cone/Cone.lean <Module> <Decl>…"
