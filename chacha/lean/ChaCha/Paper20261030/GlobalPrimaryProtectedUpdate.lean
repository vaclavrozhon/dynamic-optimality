import ChaCha.Paper20261030.GlobalPrimaryHeadLayout
import ChaCha.Paper20261030.GlobalPrimaryCacheTransport
import ChaCha.Paper20261030.HeadCacheFrameProtection

set_option autoImplicit false

/-! Assembly of a complete head successor from local output descriptions.
The cache input is a physical-id frame, which can be composed across the
actual phases. Ghost canonical occurrences of every untouched component
are derived from the output layout; they are not supplied by a runtime
table or by a successful-access hypothesis. -/

namespace ChaCha.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage SourcePointer Structural SourcePositions MultiSourceProgram
open PreferredProjection PrimaryWings Secondary SecondaryDecomposition

variable {α η F : Type*} [DecidableEq α] [DecidableEq η]

theorem StoredAt.transport_protected {before after : Source α (Cell η)} {guarded : Nat → Prop}
    (data : ComponentData α η) (old : Cursor α (Cell η)) (oldTree : old.tree = before)
    (stored : StoredAt data old)
    (occurrence : ErasedOccurrence data ((after.mapRecords Prod.fst).mapRecords Prod.snd))
    (frame : HeadCacheFrame.Protects Prod.fst guarded before after)
    (covered : guarded old.focus.rootRecord.1.1)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup) :
    ∃ actual : Cursor α (Cell η), actual.tree = after ∧ StoredAt data actual ∧
      actual.focus.rootRecord.1.1 = old.focus.rootRecord.1.1 := by
  obtain ⟨saved,ancestors,whole⟩ := occurrence
  let view : Cursor α (Packet η) := ⟨data.config.tree.setRoot (saved ++ data.config.tree.rootRecord),ancestors⟩
  have viewTree : view.tree = (after.mapRecords Prod.fst).mapRecords Prod.snd := whole.symm
  have normalized : view.focus.setRoot data.config.tree.rootRecord = data.config.tree := by
    change (data.config.tree.setRoot _).setRoot _ = _
    cases data.config.tree <;> rfl
  obtain ⟨actual,actualTree,erases,identity,_⟩ := HeadCacheFrame.retained_payload_ghost
    leafWord order distinct old oldTree view viewTree data.config.tree.rootRecord data.config.tree.rootRecord
    ((stored.normalized data old).trans normalized.symm)
  have cache := frame.cache_at old actual oldTree actualTree identity covered
  refine ⟨actual,actualTree,⟨cache.trans stored.1,saved,?_⟩,identity⟩
  exact congrArg Cursor.focus erases

/-- Physical root ids of precisely the endpoint components untouched by
the head exchange. Every cursor and endpoint witness in this predicate
is ghost data used to state a cache frame. -/
def UntouchedIds (primary : PrefRouter α) (data : α → ComponentData α η)
    (tree : Source α (Cell η)) (next : α) (ident : Nat) : Prop :=
  ∃ start subtree, ComponentRoot primary start subtree ∧
    subtree.terminal ≠ primary.terminal ∧ subtree.terminal ≠ next ∧
    ∃ current : Cursor α (Cell η), current.tree = tree ∧ StoredAt (data subtree.terminal) current ∧
      ident = current.focus.rootRecord.1.1

/-- Given the actual two final endpoint caches and a composed physical
cache frame, all other component caches follow from the finite nested
representation. The logical and nested output hypotheses are supplied
by `LogicalInvariant.head_outputs` and `Nested.head_payload_outputs`. -/
theorem Maintained.head_outputs [DecidableEq F] {height d : Nat} {markerId headerKey : Nat}
    {rank : α → Int} {reference : DepthTree 0 height} {primary successor : PrefRouter α}
    {x : α} (step : PrefRouter.HeadStep x d primary successor)
    {perfect : primary.Perfect height} {memory : MemoryKey → Bool} {data : α → ComponentData α η}
    {before after : Configuration F α (Cell η)}
    (valid : Maintained markerId headerKey rank reference primary perfect memory data before)
    (dormant active : ComponentData α η) (nextMemory : MemoryKey → Bool)
    (logical : LogicalInvariant reference successor (step.perfect perfect) nextMemory
      (Function.update (Function.update data primary.terminal dormant) successor.terminal active))
    (nested : Nested headerKey rank successor
      (Function.update (Function.update data primary.terminal dormant) successor.terminal active))
    (root : (after.tree.mapRecords Prod.fst).mapRecords Prod.snd = active.config.tree)
    (activeCache : after.tree.rootRecord.2 = some active.header)
    (dormantRoot : Cursor α (Cell η)) (dormantTree : dormantRoot.tree = after.tree)
    (dormantStored : StoredAt dormant dormantRoot)
    (physical : CanonicalComponentUniqueness.Valid markerId (after.mapRecords Prod.fst).tree)
    (reserved : markerId ∉ (after.mapRecords Prod.fst).tree.inventory Prod.fst)
    (wellFormed : WellFormed after)
    (order : after.tree.inorderLabels (fun record => record.1.1) = before.tree.inorderLabels (fun record => record.1.1))
    (frame : HeadCacheFrame.Protects Prod.fst (UntouchedIds primary data before.tree successor.terminal)
      before.tree after.tree) :
    Maintained markerId headerKey rank reference successor (step.perfect perfect) nextMemory
      (Function.update (Function.update data primary.terminal dormant) successor.terminal active) after := by
  let updated := Function.update (Function.update data primary.terminal dormant) successor.terminal active
  have different := step.endpoints_ne valid.distinct
  have distinct : successor.leaves.Nodup := by rw [step.leaves]; exact valid.distinct
  have rootView : (after.tree.mapRecords Prod.fst).mapRecords Prod.snd =
      (updated successor.terminal).config.tree := by
    simpa only [updated,Function.update_self] using root
  have afterLeaves : after.tree.shape.leaves = successor.leaves := by
    have shapes := congrArg (fun tree : Source α (Packet η) => tree.shape.leaves) rootView
    simp only [Source.mapRecords_shape] at shapes
    rw [shapes]
    exact nested.original_keys reference (step.perfect perfect) distinct nextMemory updated logical .root
  have leafWord : before.tree.shape.leaves = after.tree.shape.leaves := by
    rw [valid.original_keys,afterLeaves,step.leaves]
  have beforeDistinct : before.tree.shape.leaves.Nodup := valid.original_keys.symm ▸ valid.distinct
  refine ⟨distinct,logical,nested,rootView,?_,physical,reserved,wellFormed⟩
  intro start subtree rooted
  by_cases newActive : subtree.terminal = successor.terminal
  · refine ⟨⟨after.tree,[]⟩,rfl,?_,[],?_⟩
    · simpa only [newActive,Function.update_self] using activeCache
    · simp only [newActive,Function.update_self]
      change (after.tree.mapRecords Prod.fst).mapRecords Prod.snd = _
      rw [root,List.nil_append]
      cases active.config.tree <;> rfl
  · by_cases oldActive : subtree.terminal = primary.terminal
    · refine ⟨dormantRoot,dormantTree,?_⟩
      simpa only [oldActive,Function.update_of_ne different,Function.update_self] using dormantStored
    · have oldRoot := (ComponentRoot.head_other_iff step oldActive newActive).mp rooted
      obtain ⟨old,oldTree,oldStored⟩ := valid.stored oldRoot
      have covered : UntouchedIds primary data before.tree successor.terminal old.focus.rootRecord.1.1 :=
        ⟨start,subtree,oldRoot,oldActive,newActive,old,oldTree,oldStored,rfl⟩
      have unchanged : updated subtree.terminal = data subtree.terminal :=
        head_data_untouched data _ _ _ dormant active oldActive newActive
      have occurrence : ErasedOccurrence (data subtree.terminal)
          ((after.tree.mapRecords Prod.fst).mapRecords Prod.snd) := by
        rw [rootView]
        have occurs := nested.erased_occurs reference (step.perfect perfect) distinct nextMemory updated logical rooted
        rw [unchanged] at occurs
        exact occurs
      obtain ⟨actual,actualTree,stored,_⟩ := oldStored.transport_protected (data subtree.terminal) old oldTree
        occurrence frame covered leafWord order beforeDistinct
      refine ⟨actual,actualTree,?_⟩
      simpa only [Function.update_of_ne newActive,Function.update_of_ne oldActive] using stored

end ChaCha.Paper20261030.GlobalPrimaryRepresentation
