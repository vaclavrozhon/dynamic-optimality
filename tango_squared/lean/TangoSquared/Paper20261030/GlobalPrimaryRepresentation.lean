import TangoSquared.Paper20261030.GlobalPrimaryComponents
import TangoSquared.Paper20261030.MaintainedPhysicalState
import TangoSquared.Paper20261030.CachedReachedRootedOperation

set_option autoImplicit false

/-! A concrete ghost description of the whole maintained primary tree.
Each endpoint describes one decorated secondary source, its canonical
tagged forest, its actual nested assembly, and its stored root header.
Only endpoints in the finite primary leaf word are relevant. No table,
source tree, assembly, cursor, or path below is a runtime input.

The invariant asserts the current representation. It contains no assumed
preservation theorem and no successful access run. Its logical replacement
lemma accepts the actual two local outputs; its recursive layout lemma
derives the original-key word from the nested canonical assemblies. -/

namespace TangoSquared.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent
open BoundaryObservations PathDecomposition PreferredProjection PrimaryWings Secondary SecondaryDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram

local instance globalPrimaryColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Packet (η : Type*) := EnclosedRootedComponentExecution.Packet Nat Cached Nat η
abbrev RawCell (η : Type*) := EnclosedRootedComponentExecution.Cell Nat Cached Nat η
abbrev Cell (η : Type*) := CachedRootedComponentExecution.CachedCell Nat Cached Nat η
abbrev LogicalRecord (η : Type*) := LocalColoredCompiler.LogicalRecord Cached η (Option Bool)

/-- A component description used only in proofs. Actual header acquisition
is performed by the existing cached-root controllers. -/
structure ComponentData (α η : Type*) where
  component : AuxiliaryComponent Nat Nat (Tagged Payload)
  decorated : Source Nat (η × Cached)
  forest : TaggedForest (Option Bool) Nat (LogicalRecord η) Nat
  payload : Option Bool → Nat → Source α (Packet η)
  config : Configuration (Option Bool) α (Packet η)
  header : PrimaryHeaderController.Header η

variable {α η F : Type*} [DecidableEq α] [DecidableEq η]

def components (data : α → ComponentData α η) : Components α := fun key => (data key).component
def inventories (data : α → ComponentData α η) : α → Multiset η :=
  fun key => (data key).decorated.inventory Prod.fst

structure Canonical (headerKey : Nat) (data : ComponentData α η)
    (color : Nat → Option Bool) (bottom : Int) (start : Nat) : Prop where
  erases : data.decorated.mapRecords Prod.snd = closed data.component
  forestRep : ProjectionForest.Represents color
    ⟨annotate Prod.fst color none data.decorated,[]⟩ (erase data.forest)
  physicalUnique : PhysicalForestMetadata.Unique data.forest
  assembled : ForestConnector.assemble
    (representation none wingOrientation headerKey data.payload data.forest)
    (layout (representation none wingOrientation headerKey data.payload data.forest)) = some data.config
  headerRep : PrimaryHeaderController.Represents data.header bottom start
    data.decorated data.forest headerKey data.payload

/-- The component cursor is a ghost occurrence. Its enclosing root packet
may come from the parent's routing leaf or several canonical outer layers. -/
def StoredAt (data : ComponentData α η) (current : Cursor α (Cell η)) : Prop :=
  current.focus.rootRecord.2 = some data.header ∧
    ∃ saved : Packet η,
      (current.focus.mapRecords Prod.fst).mapRecords Prod.snd =
        data.config.tree.setRoot (saved ++ data.config.tree.rootRecord)

structure LogicalInvariant {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (memory : MemoryKey → Bool)
    (data : α → ComponentData α η) : Prop where
  represented : Components.Valid reference primary perfect memory (components data)
  unique : GlobalPrimaryInventory.Unique primary.leaves.toFinset (inventories data)

/-- Each genuine depth port is exactly the canonical assembly of the
corresponding child component; the virtual payload is its bottom key. -/
structure Nested (headerKey : Nat) (rank : α → Int) (primary : PrefRouter α)
    (data : α → ComponentData α η) : Prop where
  canonical : ∀ {start subtree}, ComponentRoot primary start subtree →
    Canonical headerKey (data subtree.terminal) (PackedPrimary.color start subtree)
      (rank subtree.terminal) start
  child : ∀ {start subtree depth exit}, ComponentRoot primary start subtree →
    portAt 0 (exits subtree) depth = some exit →
    (data subtree.terminal).payload (some exit.leftOfEndpoint) (start+depth) =
      (data exit.subtree.terminal).config.tree
  bottom : ∀ {start subtree}, ComponentRoot primary start subtree →
    ((data subtree.terminal).payload none headerKey).shape.leaves = [subtree.terminal]

/-- Global state at primary request boundaries. Distinct physical ids and
canonical packet alignment refer to the same shared stored tree. -/
structure Maintained [DecidableEq F] {height : Nat} (markerId headerKey : Nat)
    (rank : α → Int) (reference : DepthTree 0 height) (primary : PrefRouter α)
    (perfect : primary.Perfect height) (memory : MemoryKey → Bool)
    (data : α → ComponentData α η) (shared : Configuration F α (Cell η)) : Prop where
  distinct : primary.leaves.Nodup
  logical : LogicalInvariant reference primary perfect memory data
  nested : Nested headerKey rank primary data
  root : (shared.tree.mapRecords Prod.fst).mapRecords Prod.snd = (data primary.terminal).config.tree
  stored : ∀ {start subtree}, ComponentRoot primary start subtree →
    ∃ current : Cursor α (Cell η), current.tree = shared.tree ∧ StoredAt (data subtree.terminal) current
  physical : CanonicalComponentUniqueness.Valid markerId (shared.mapRecords Prod.fst).tree
  reserved : markerId ∉ (shared.mapRecords Prod.fst).tree.inventory Prod.fst
  wellFormed : WellFormed shared

theorem components_update (data : α → ComponentData α η) (key : α) (fresh : ComponentData α η) :
    components (Function.update data key fresh) = Function.update (components data) key fresh.component := by
  funext other
  by_cases equal : other = key
  · subst other; simp only [components,Function.update_self]
  · simp only [components,Function.update_of_ne equal]

theorem inventories_update (data : α → ComponentData α η) (key : α) (fresh : ComponentData α η) :
    inventories (Function.update data key fresh) =
      Function.update (inventories data) key (fresh.decorated.inventory Prod.fst) := by
  funext other
  by_cases equal : other = key
  · subst other; simp only [inventories,Function.update_self]
  · simp only [inventories,Function.update_of_ne equal]

theorem LogicalInvariant.component_unique {height : Nat} {reference : DepthTree 0 height}
    {primary : PrefRouter α} {perfect : primary.Perfect height} {memory : MemoryKey → Bool}
    {data : α → ComponentData α η} (valid : LogicalInvariant reference primary perfect memory data)
    {key : α} (member : key ∈ primary.leaves) : ((data key).decorated.inventory Prod.fst).Nodup :=
  valid.unique.component (List.mem_toFinset.mpr member)

theorem LogicalInvariant.head_joint {height d : Nat} {reference : DepthTree 0 height}
    {x : α} {before after : PrefRouter α} {perfect : before.Perfect height} {memory : MemoryKey → Bool}
    {data : α → ComponentData α η} (valid : LogicalInvariant reference before perfect memory data)
    (step : PrefRouter.HeadStep x d before after) (distinct : before.leaves.Nodup) :
    ((data before.terminal).decorated.inventory Prod.fst +
      (data after.terminal).decorated.inventory Prod.fst).Nodup :=
  head_joint_inventory step distinct (inventories data) valid.unique

theorem LogicalInvariant.head_outputs {height d : Nat} (reference : DepthTree 0 height)
    (depth : d ≤ height) {x : α} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) (distinct : before.leaves.Nodup)
    (perfect : before.Perfect height) (memory : MemoryKey → Bool)
    (data : α → ComponentData α η) (valid : LogicalInvariant reference before perfect memory data)
    (dormant active : ComponentData α η)
    (activeRep : Represents followsRight
      (source reference (spliceBits d (intervalUpdate d (ownerBits before before.terminal memory))
        (intervalUpdate d (ownerBits before after.terminal memory)))) active.component)
    (dormantRep : Represents followsRight
      (suffixSource reference (intervalUpdate d (ownerBits before before.terminal memory))
        d ⟨Nat.zero_le _,depth⟩) dormant.component)
    (pair : active.decorated.inventory Prod.fst + dormant.decorated.inventory Prod.fst =
      (data before.terminal).decorated.inventory Prod.fst + (data after.terminal).decorated.inventory Prod.fst) :
    LogicalInvariant reference after (step.perfect perfect) (advanceDepth before x d memory)
      (Function.update (Function.update data before.terminal dormant) after.terminal active) := by
  constructor
  · rw [components_update,components_update]
    exact valid.represented.prepared_head_outputs reference depth step distinct perfect memory
      (components data) dormant.component active.component activeRep dormantRep
  · rw [inventories_update,inventories_update]
    exact head_inventory_unique step distinct (inventories data) valid.unique _ _ pair

theorem head_data_untouched (data : α → ComponentData α η) (old fresh key : α)
    (dormant active : ComponentData α η) (notOld : key ≠ old) (notFresh : key ≠ fresh) :
    Function.update (Function.update data old dormant) fresh active key = data key := by
  simp only [Function.update_of_ne notFresh,Function.update_of_ne notOld]

theorem Canonical.ports {height start : Nat} (reference : DepthTree 0 height)
    {whole subtree : PrefRouter α} (perfect : whole.Perfect height) (distinct : whole.leaves.Nodup)
    (memory : MemoryKey → Bool) (data : α → ComponentData α η)
    (valid : LogicalInvariant reference whole perfect memory data)
    (rooted : ComponentRoot whole start subtree) {headerKey : Nat} {rank : α → Int}
    (canonical : Canonical headerKey (data subtree.terminal) (PackedPrimary.color start subtree)
      (rank subtree.terminal) start) :
    (data subtree.terminal).decorated.shape.leaves.filterMap (portAt start (exits subtree)) = exits subtree := by
  have input := valid.represented.input reference perfect distinct memory (components data) rooted
  rw [rooted.endpoint_start distinct] at input
  have ports := (PackedPrimary.Input.mk start (closed (data subtree.terminal).component) input).ports
  have shape := congrArg (fun tree : Source Nat Cached => tree.shape.leaves) canonical.erases
  simp only [Source.mapRecords_shape] at shape
  rw [shape]
  exact ports

end TangoSquared.Paper20261030.GlobalPrimaryRepresentation
