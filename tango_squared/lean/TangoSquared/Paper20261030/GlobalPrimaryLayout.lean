import TangoSquared.Paper20261030.GlobalPrimaryRepresentation
import TangoSquared.Paper20261030.GlobalPrimaryRoots

set_option autoImplicit false

/-! Canonical nested assemblies have the original-key leaf word. A head
exchange changes only two endpoint descriptions: every other component
retains its exact subtree, source, forest, assembly, header, and child links.
The changed descriptions are supplied by the actual local outputs. -/

namespace TangoSquared.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent
open BoundaryObservations PathDecomposition PreferredProjection PrimaryWings Secondary SecondaryDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram

variable {α η : Type*} [DecidableEq α] [DecidableEq η]

theorem Nested.original_keys {height start : Nat} (reference : DepthTree 0 height)
    {whole subtree : PrefRouter α} (perfect : whole.Perfect height) (distinct : whole.leaves.Nodup)
    (memory : MemoryKey → Bool) (data : α → ComponentData α η)
    (valid : LogicalInvariant reference whole perfect memory data) {headerKey : Nat} {rank : α → Int}
    (nested : Nested headerKey rank whole data) (rooted : ComponentRoot whole start subtree) :
    (data subtree.terminal).config.tree.shape.leaves = subtree.leaves := by
  have canonical := nested.canonical rooted
  apply LocalComponentCompiler.original_keys start subtree ⟨(data subtree.terminal).decorated,[]⟩
    (canonical.ports reference perfect distinct memory data valid rooted)
    (data subtree.terminal).forest canonical.forestRep headerKey (data subtree.terminal).payload
    _ (nested.bottom rooted) (data subtree.terminal).config canonical.assembled
  intro side key selected
  have found : ∃ exit, portAt start (exits subtree) key = some exit ∧ exit.leftOfEndpoint = side := by
    unfold PackedPrimary.color at selected
    cases present : portAt start (exits subtree) key with
    | none => simp only [present,Option.map_none,reduceCtorEq] at selected
    | some exit => exact ⟨exit,rfl,by simpa only [present,Option.map_some,Option.some.injEq] using selected⟩
  obtain ⟨exit,present,sideEq⟩ := found
  have afterStart : start ≤ key := by
    by_contra absent
    simp only [portAt,if_neg absent,reduceCtorEq] at present
  have localFound : portAt 0 (exits subtree) (key-start) = some exit := by
    simpa only [portAt,if_pos afterStart,Nat.zero_le,if_true,Nat.sub_zero] using present
  have attached := nested.child rooted localFound
  rw [Nat.add_sub_of_le afterStart,sideEq] at attached
  rw [attached,PackedPrimary.label,present,Option.getD_some]
  exact nested.original_keys reference perfect distinct memory data valid (rooted.child localFound)
termination_by subtree.leaves.length
decreasing_by
  exact exit_smaller (List.mem_of_getElem? (by simpa [portAt] using localFound))

theorem Maintained.original_keys {F : Type*} [DecidableEq F] {height : Nat}
    {markerId headerKey : Nat} {rank : α → Int} {reference : DepthTree 0 height}
    {primary : PrefRouter α} {perfect : primary.Perfect height} {memory : MemoryKey → Bool}
    {data : α → ComponentData α η} {shared : Configuration F α (Cell η)}
    (valid : Maintained markerId headerKey rank reference primary perfect memory data shared) :
    shared.tree.shape.leaves = primary.leaves := by
  have shape := congrArg (fun tree : Source α (Packet η) => tree.shape.leaves) valid.root
  simp only [Source.mapRecords_shape] at shape
  rw [shape]
  exact valid.nested.original_keys reference perfect valid.distinct memory data valid.logical .root

structure ComponentLayout (headerKey : Nat) (rank : α → Int) (data : α → ComponentData α η)
    (start : Nat) (subtree : PrefRouter α) : Prop where
  canonical : Canonical headerKey (data subtree.terminal) (PackedPrimary.color start subtree)
    (rank subtree.terminal) start
  child : ∀ {depth exit}, portAt 0 (exits subtree) depth = some exit →
    (data subtree.terminal).payload (some exit.leftOfEndpoint) (start+depth) =
      (data exit.subtree.terminal).config.tree
  bottom : ((data subtree.terminal).payload none headerKey).shape.leaves = [subtree.terminal]

theorem Nested.component {headerKey : Nat} {rank : α → Int} {primary : PrefRouter α}
    {data : α → ComponentData α η} (nested : Nested headerKey rank primary data)
    {start : Nat} {subtree : PrefRouter α} (rooted : ComponentRoot primary start subtree) :
    ComponentLayout headerKey rank data start subtree :=
  ⟨nested.canonical rooted,nested.child rooted,nested.bottom rooted⟩

/-- Every child of an untouched component also avoids both changed endpoints.
Thus replacing the endpoint table leaves all its canonical child links intact. -/
theorem Nested.head_untouched {headerKey : Nat} {rank : α → Int} {d start : Nat}
    {x : α} {before after subtree : PrefRouter α} {data : α → ComponentData α η}
    (nested : Nested headerKey rank before data) (step : PrefRouter.HeadStep x d before after)
    (distinct : before.leaves.Nodup) (rooted : ComponentRoot after start subtree)
    (oldOther : subtree.terminal ≠ before.terminal) (newOther : subtree.terminal ≠ after.terminal)
    (dormant active : ComponentData α η) :
    ComponentLayout headerKey rank
      (Function.update (Function.update data before.terminal dormant) after.terminal active) start subtree := by
  have beforeRoot := (ComponentRoot.head_other_iff step oldOther newOther).mp rooted
  have afterDistinct : after.leaves.Nodup := by rw [step.leaves]; exact distinct
  have oldExcluded := beforeRoot.excludes_active distinct oldOther
  have newExcluded := rooted.excludes_active afterDistinct newOther
  have parentSame := head_data_untouched data before.terminal after.terminal subtree.terminal
    dormant active oldOther newOther
  constructor
  · rw [parentSame]
    exact nested.canonical beforeRoot
  · intro depth exit present
    have member := exit_leaves_subset (List.mem_of_getElem? (by simpa [portAt] using present))
      exit.subtree.terminal exit.subtree.terminal_mem
    have childOld : exit.subtree.terminal ≠ before.terminal := by
      intro same; exact oldExcluded (same ▸ member)
    have childNew : exit.subtree.terminal ≠ after.terminal := by
      intro same; exact newExcluded (same ▸ member)
    rw [parentSame,head_data_untouched data before.terminal after.terminal exit.subtree.terminal
      dormant active childOld childNew]
    exact nested.child beforeRoot present
  · rw [parentSame]
    exact nested.bottom beforeRoot

/-- Concrete layout replacement needs local output layouts only for the
new active component and the new dormant component. All untouched layouts
are proved by the preceding frame lemma. -/
theorem Nested.head_update {headerKey : Nat} {rank : α → Int} {d : Nat}
    {x : α} {before after old : PrefRouter α} {data : α → ComponentData α η}
    (nested : Nested headerKey rank before data) (step : PrefRouter.HeadStep x d before after)
    (distinct : before.leaves.Nodup) (oldRoot : ComponentRoot after (d+1) old)
    (oldEndpoint : old.terminal = before.terminal) (dormant active : ComponentData α η)
    (activeLayout : ComponentLayout headerKey rank
      (Function.update (Function.update data before.terminal dormant) after.terminal active) 0 after)
    (dormantLayout : ComponentLayout headerKey rank
      (Function.update (Function.update data before.terminal dormant) after.terminal active) (d+1) old) :
    Nested headerKey rank after
      (Function.update (Function.update data before.terminal dormant) after.terminal active) := by
  have afterDistinct : after.leaves.Nodup := by rw [step.leaves]; exact distinct
  have every : ∀ {start subtree}, ComponentRoot after start subtree → ComponentLayout headerKey rank
      (Function.update (Function.update data before.terminal dormant) after.terminal active) start subtree := by
    intro start subtree rooted
    by_cases newEnd : subtree.terminal = after.terminal
    · obtain ⟨rfl,rfl⟩ := rooted.eq_root_of_terminal afterDistinct newEnd
      exact activeLayout
    · by_cases oldEnd : subtree.terminal = before.terminal
      · obtain ⟨rfl,rfl⟩ := rooted.endpoint_unique oldRoot afterDistinct (oldEnd.trans oldEndpoint.symm)
        exact dormantLayout
      · exact nested.head_untouched step distinct rooted oldEnd newEnd dormant active
  exact ⟨fun rooted => (every rooted).canonical,
    fun rooted present => (every rooted).child present,fun rooted => (every rooted).bottom⟩

end TangoSquared.Paper20261030.GlobalPrimaryRepresentation
