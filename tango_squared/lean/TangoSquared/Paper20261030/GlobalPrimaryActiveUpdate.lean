import TangoSquared.Paper20261030.GlobalPrimaryCacheTransport
import TangoSquared.Paper20261030.GlobalPrimaryPreparation

set_option autoImplicit false

/-! A root-to-root source operation updates exactly the active endpoint.
Its fixed payloads preserve the entire nested layout. Its singleton cache
frame preserves every other component's actual stored header, because
all these components have proper canonical output occurrences. -/

namespace TangoSquared.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent
open BoundaryObservations PathDecomposition PreferredProjection PrimaryWings Secondary SecondaryDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram

variable {α η F : Type*} [DecidableEq α] [DecidableEq η]

theorem Nested.active_output {headerKey : Nat} {rank : α → Int} {primary : PrefRouter α}
    {data : α → ComponentData α η} (nested : Nested headerKey rank primary data)
    (distinct : primary.leaves.Nodup) (fresh : ComponentData α η)
    (canonical : Canonical headerKey fresh (PackedPrimary.color 0 primary) (rank primary.terminal) 0)
    (payload : fresh.payload = (data primary.terminal).payload) :
    Nested headerKey rank primary (Function.update data primary.terminal fresh) := by
  have every : ∀ {start subtree}, ComponentRoot primary start subtree →
      ComponentLayout headerKey rank (Function.update data primary.terminal fresh) start subtree := by
    intro start subtree rooted
    by_cases active : subtree.terminal = primary.terminal
    · obtain ⟨startEq,subtreeEq⟩ := rooted.eq_root_of_terminal distinct active
      subst start
      subst subtree
      constructor
      · simpa only [Function.update_self] using canonical
      · intro depth exit present
        have childRoot : ComponentRoot primary (depth+1) exit.subtree := by
          simpa only [Nat.zero_add] using ComponentRoot.child (.root : ComponentRoot primary 0 primary) present
        have other : exit.subtree.terminal ≠ primary.terminal := by
          intro same
          have zero := (childRoot.eq_root_of_terminal distinct same).1
          omega
        rw [Function.update_self,Function.update_of_ne other,payload]
        exact nested.child (.root : ComponentRoot primary 0 primary) present
      · rw [Function.update_self,payload]
        exact nested.bottom (.root : ComponentRoot primary 0 primary)
    · have excluded := rooted.excludes_active distinct active
      constructor
      · simpa only [Function.update_of_ne active] using nested.canonical rooted
      · intro depth exit present
        have member := exit_leaves_subset (List.mem_of_getElem? (by simpa [portAt] using present))
          exit.subtree.terminal exit.subtree.terminal_mem
        have other : exit.subtree.terminal ≠ primary.terminal := by intro same; exact excluded (same ▸ member)
        rw [Function.update_of_ne active,Function.update_of_ne other]
        exact nested.child rooted present
      · simpa only [Function.update_of_ne active] using nested.bottom rooted
  exact ⟨fun rooted => (every rooted).canonical,
    fun rooted present => (every rooted).child present,fun rooted => (every rooted).bottom⟩

/-- Full global representation preservation for one active source phase.
All inputs after `fresh` are actual local output facts: its represented
source and assembly, fixed payloads, physical validity, inorder ids, and
the one-root cache frame. No output cache occurrence is assumed for an
untouched endpoint. -/
theorem Maintained.active_output [DecidableEq F] {height : Nat} {markerId headerKey : Nat}
    {rank : α → Int} {reference : DepthTree 0 height} {primary : PrefRouter α}
    {perfect : primary.Perfect height} {memory : MemoryKey → Bool} {data : α → ComponentData α η}
    {before after : Configuration F α (Cell η)}
    (valid : Maintained markerId headerKey rank reference primary perfect memory data before)
    (fresh : ComponentData α η) (nextMemory : MemoryKey → Bool)
    (logical : LogicalInvariant reference primary perfect nextMemory (Function.update data primary.terminal fresh))
    (canonical : Canonical headerKey fresh (PackedPrimary.color 0 primary) (rank primary.terminal) 0)
    (payload : fresh.payload = (data primary.terminal).payload)
    (root : (after.tree.mapRecords Prod.fst).mapRecords Prod.snd = fresh.config.tree)
    (cache : after.tree.rootRecord.2 = some fresh.header)
    (physical : CanonicalComponentUniqueness.Valid markerId (after.mapRecords Prod.fst).tree)
    (reserved : markerId ∉ (after.mapRecords Prod.fst).tree.inventory Prod.fst)
    (wellFormed : WellFormed after)
    (order : after.tree.inorderLabels (fun record => record.1.1) = before.tree.inorderLabels (fun record => record.1.1))
    (frame : HeadCacheFrame.MetadataFrame Prod.fst [after.tree.rootRecord.1.1] before.tree after.tree) :
    Maintained markerId headerKey rank reference primary perfect nextMemory
      (Function.update data primary.terminal fresh) after := by
  let updated := Function.update data primary.terminal fresh
  have nested := valid.nested.active_output valid.distinct fresh canonical payload
  have rootView : (after.tree.mapRecords Prod.fst).mapRecords Prod.snd = (updated primary.terminal).config.tree := by
    simpa only [updated,Function.update_self] using root
  have afterLeaves : after.tree.shape.leaves = primary.leaves := by
    have shapes := congrArg (fun tree : Source α (Packet η) => tree.shape.leaves) rootView
    simp only [Source.mapRecords_shape] at shapes
    rw [shapes]
    exact nested.original_keys reference perfect valid.distinct nextMemory updated logical .root
  have leafWord : before.tree.shape.leaves = after.tree.shape.leaves := valid.original_keys.trans afterLeaves.symm
  have beforeDistinct : before.tree.shape.leaves.Nodup := valid.original_keys.symm ▸ valid.distinct
  have unique : (after.tree.inventory (fun record => record.1.1)).Nodup := by
    simpa only [Configuration.mapRecords,mapRecords_inventory,Function.comp_def] using physical.2.2
  refine ⟨valid.distinct,logical,nested,rootView,?_,physical,reserved,wellFormed⟩
  intro start subtree rooted
  by_cases active : subtree.terminal = primary.terminal
  · refine ⟨⟨after.tree,[]⟩,rfl,?_,[],?_⟩
    · simpa only [active,updated,Function.update_self] using cache
    · simp only [active,Function.update_self]
      change (after.tree.mapRecords Prod.fst).mapRecords Prod.snd = _
      rw [root,List.nil_append]
      cases fresh.config.tree <;> rfl
  · obtain ⟨old,oldTree,oldStored⟩ := valid.stored rooted
    have unchanged : updated subtree.terminal = data subtree.terminal := Function.update_of_ne active ..
    obtain ⟨saved,inside,proper,occurrence⟩ := nested.proper_erased_occurs reference perfect valid.distinct
      nextMemory updated logical rooted active
    have parentView : (after.tree.mapRecords Prod.fst).mapRecords Prod.snd =
        plug ((data subtree.terminal).config.tree.setRoot
          (saved ++ (data subtree.terminal).config.tree.rootRecord)) inside := by
      rw [rootView,occurrence,unchanged]
    obtain ⟨actual,actualTree,stored,_,_⟩ := oldStored.transport_proper (data subtree.terminal) old oldTree
      ⟨after.tree,[]⟩ rfl saved inside proper parentView frame leafWord order beforeDistinct unique
    refine ⟨actual,actualTree,?_⟩
    simpa only [Function.update_of_ne active] using stored

end TangoSquared.Paper20261030.GlobalPrimaryRepresentation
