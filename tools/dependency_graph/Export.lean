import Lean

/-!
Read direct dependencies from Lean's elaborated declarations. `export.py` places
the body of this file after imports of every registered, tracked local module.
The generated driver deliberately does not use the `module` command: Lean then
loads private declarations and theorem bodies as well as public declarations.

The exporter is tooling, not a new declaration in the mathematical libraries.
It writes JSON Lines so the large graph need not be assembled inside Lean.
-/

open Lean

namespace DependencyGraph

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => throw <| IO.userError e

private def getString (j : Json) (key : String) : IO String := do
  match j.getObjValAs? String key with
  | .ok s => pure s
  | .error e => throw <| IO.userError e

/-- Include structure names stored in projection expressions as references. -/
private def references (e : Expr) : IO NameSet := do
  let found ← IO.mkRef ({} : NameSet)
  e.forEach fun e => do
    match e with
    | .const n _ | .proj n _ _ => found.modify (·.insert n)
    | _ => pure ()
  found.get

/-- Recursor reduction rules are elaborated value expressions, too. -/
private def valueReferences (info : ConstantInfo) : IO NameSet := do
  if let some e := info.value? (allowOpaque := true) then
    return ← references e
  match info with
  | .recInfo r =>
    let mut found : NameSet := {}
    for rule in r.rules do
      found := found ++ (← references rule.rhs)
    return found
  | _ => return {}

private def write (handle : IO.FS.Handle) (j : Json) : IO Unit :=
  handle.putStrLn j.compress

def exportGraph (env : Environment) (manifestPath outputPath : System.FilePath) : IO Unit := do
  IO.eprintln "Dependency graph: imports loaded; identifying local declarations."
  -- `EnvironmentHeader.moduleNames` computes an array; do not rebuild it per edge.
  let moduleNames := env.header.moduleNames
  let manifest ← readJson manifestPath
  let modules ← match manifest.getObjValAs? (Array Json) "modules" with
    | .ok a => pure a
    | .error e => throw <| IO.userError e
  let mut moduleMap : NameMap (String × String) := {}
  for entry in modules do
    moduleMap := moduleMap.insert (← getString entry "module").toName
      (← getString entry "file", ← getString entry "group")
  let mut names : Array Name := #[]
  let mut scanned := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if moduleMap.contains moduleNames[idx]! then
        names := names.push name
    scanned := scanned + 1
    if scanned % 100000 == 0 then
      IO.eprintln s!"Dependency graph: inspected {scanned} imported constants; {names.size} local."
  IO.eprintln s!"Dependency graph: sorting {names.size} local declaration names."
  names := names.qsort Name.lt
  let mut ids : NameMap Nat := {}
  for i in [:names.size] do
    ids := ids.insert names[i]! i
  let output ← IO.FS.Handle.mk outputPath .write
  IO.eprintln s!"Dependency graph: scanning {names.size} local declarations."
  let mut edgeCount := 0
  let mut externalCount := 0
  let mut externalTypeCount := 0
  let mut externalValueCount := 0
  let mut externalNames : NameSet := {}
  let mut externalModules : NameSet := {}
  let mut missingConstants : NameSet := {}
  let mut importedLocalModules : NameSet := {}
  for i in [:names.size] do
    let name := names[i]!
    let some info := env.find? name
      | throw <| IO.userError s!"Missing declaration: {name}"
    let some idx := env.getModuleIdxFor? name
      | throw <| IO.userError s!"Missing module provenance: {name}"
    let mod := moduleNames[idx]!
    let some (file, group) := moduleMap.find? mod
      | throw <| IO.userError s!"Missing local source: {mod}"
    importedLocalModules := importedLocalModules.insert mod
    let ranges := declRangeExt.find? (level := .exported) env name <|>
      declRangeExt.find? (level := .server) env name
    let userName := privateToUserName name
    let generated := userName.isInternalDetail || ranges.isNone || (info matches .recInfo _)
    let line : Json := match ranges with
      | some r => toJson r.selectionRange.pos.line
      | none => .null
    let typeRefs ← references info.type
    let valueRefs ← valueReferences info
    let allRefs := typeRefs ++ valueRefs
    let mut external := 0
    for target in allRefs.toArray.qsort Name.lt do
      let mask := (if typeRefs.contains target then 1 else 0) +
        (if valueRefs.contains target then 2 else 0)
      if let some j := ids.find? target then
        write output <| Json.mkObj [("edge", toJson #[i, j, mask])]
        edgeCount := edgeCount + 1
      else
        external := external + 1
        externalCount := externalCount + 1
        if typeRefs.contains target then externalTypeCount := externalTypeCount + 1
        if valueRefs.contains target then externalValueCount := externalValueCount + 1
        externalNames := externalNames.insert target
        if let some targetIdx := env.getModuleIdxFor? target then
          externalModules := externalModules.insert moduleNames[targetIdx]!
        unless env.contains target do missingConstants := missingConstants.insert target
    write output <| Json.mkObj [("node", Json.mkObj [
      ("id", toJson i), ("name", toJson name.toString),
      ("label", toJson userName.toString), ("kind", toJson (kind info)),
      ("module", toJson mod.toString), ("file", toJson file), ("line", line),
      ("group", toJson group), ("generated", toJson generated),
      ("private", toJson (isPrivateName name)),
      ("externalReferences", toJson external)])]
    if (i + 1) % 2000 == 0 then
      IO.eprintln s!"Dependency graph: {i + 1}/{names.size} declarations; {edgeCount} edges."
  write output <| Json.mkObj [("statistics", Json.mkObj [
    ("nodeCount", toJson names.size), ("edgeCount", toJson edgeCount),
    ("externalReferenceCount", toJson externalCount),
    ("externalTypeReferenceCount", toJson externalTypeCount),
    ("externalValueReferenceCount", toJson externalValueCount),
    ("externalConstantCount", toJson externalNames.size),
    ("externalModuleCount", toJson externalModules.size),
    ("unresolvedConstants", toJson (missingConstants.toArray.map Name.toString)),
    ("modulesWithDeclarations", toJson (importedLocalModules.toArray.map Name.toString)),
    ("loadedModules", toJson (moduleNames.filter moduleMap.contains |>.map Name.toString))])]
  IO.eprintln s!"Dependency graph complete: {names.size} declarations, {edgeCount} local edges."

end DependencyGraph
