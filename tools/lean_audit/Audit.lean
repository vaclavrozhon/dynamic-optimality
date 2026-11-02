import Lean

/-!
The audit runner places this helper after imports of all registered local
modules in an old-style driver, retaining private declarations. Target
selection uses exact compiler module provenance, including local lemmas in
namespaces such as `List` and compiler-generated declarations.
-/

open Lean

namespace LeanAudit

def auditRegistered (manifestPath : System.FilePath) : CoreM Unit := do
  let env ← getEnv
  -- This accessor constructs an array; cache it before scanning constants.
  let moduleNames := env.header.moduleNames
  let contents ← IO.FS.readFile manifestPath
  let manifest ← match Json.parse contents with
    | .ok value => pure value
    | .error message => throwError "Invalid audit manifest: {message}"
  let entries ← match manifest.getObjValAs? (Array Json) "modules" with
    | .ok values => pure values
    | .error message => throwError "Invalid audit module inventory: {message}"
  let mut registered : NameSet := {}
  for entry in entries do
    let name ← match entry.getObjValAs? String "module" with
      | .ok value => pure value.toName
      | .error message => throwError "Invalid registered module: {message}"
    if registered.contains name then
      throwError "Duplicate registered module in audit inventory: {name}"
    registered := registered.insert name
  if registered.isEmpty then
    throwError "The registered-module audit inventory is empty"
  let mut loaded : NameSet := {}
  for name in moduleNames do
    if registered.contains name then loaded := loaded.insert name
  let missing := registered.toArray.filter (fun name => !loaded.contains name)
  unless missing.isEmpty do
    throwError "Registered modules were not imported for the audit: {missing}"
  let mut targets : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      if registered.contains moduleNames[index]! then
        targets := targets.push name
  if targets.isEmpty then
    throwError "No declarations were found in the registered modules"
  IO.eprintln s!"Starting registered-module audit: {registered.size} modules, {targets.size} declarations (including private and generated)."
  let mut count : Nat := 0
  let mut unexpected : Array (Name × Array Name) := #[]
  for name in targets do
    let axioms ← Lean.collectAxioms name
    if axioms.any (fun ax => ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound) then
      unexpected := unexpected.push (name, axioms)
    count := count + 1
    if count % 2000 == 0 then
      IO.eprintln s!"Axiom audit progress: {count}/{targets.size}."
  logInfo m!"Audited all registered local declarations: {count}"
  logInfo m!"Declarations using nonstandard axioms: {unexpected}"
  unless unexpected.isEmpty do
    throwError "Nonstandard axiom dependency in the registered development"

end LeanAudit
