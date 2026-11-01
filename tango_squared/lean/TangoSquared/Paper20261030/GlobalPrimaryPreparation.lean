import TangoSquared.Paper20261030.GlobalPrimaryRepresentation

set_option autoImplicit false

/-! Preparing the active secondary component already maintains the owner
memory semantics on the unchanged primary tree. The subsequent head
exchange changes the primary decomposition; preparation does not leave
the other endpoint sources without a valid interpretation. -/

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection

theorem advanceDepth_idempotent {α : Type*} [DecidableEq α] (primary : PrefRouter α)
    (key : α) (depth : Nat) (memory : MemoryKey → Bool) :
    advanceDepth primary key depth (advanceDepth primary key depth memory) =
      advanceDepth primary key depth memory := by
  funext record
  simp only [advanceDepth]
  cases depthWrite primary key depth record <;> rfl

end TangoSquared.Paper20261030.Secondary

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection Secondary

variable {α : Type*} [DecidableEq α]

theorem head_prepared_owner {x : α} {d : Nat} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) (distinct : before.leaves.Nodup)
    (memory : MemoryKey → Bool) :
    ownerBits before before.terminal (advanceDepth before x d memory) =
      intervalUpdate d (ownerBits before before.terminal memory) := by
  have same : ownerBits after before.terminal (advanceDepth before x d memory) =
      ownerBits before before.terminal (advanceDepth before x d memory) := by
    funext split
    simp only [ownerBits,step.searchPath]
  rw [← same]
  exact old_tail_prepared step distinct memory

theorem Components.Valid.prepared_active_output {height d : Nat} (reference : DepthTree 0 height)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x d before after)
    (perfect : before.Perfect height) (distinct : before.leaves.Nodup) (memory : MemoryKey → Bool)
    (components : Components α) (valid : Components.Valid reference before perfect memory components)
    (fresh : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (source reference (intervalUpdate d (ownerBits before before.terminal memory))) fresh) :
    Components.Valid reference before perfect (advanceDepth before x d memory)
      (Function.update components before.terminal fresh) := by
  intro key member
  by_cases active : key = before.terminal
  · subst key
    simpa only [Function.update_self,componentSource_active,head_prepared_owner step distinct memory] using represented
  · have sourceSame : componentSource reference before perfect (advanceDepth before x d memory) key =
        componentSource reference before perfect memory key := by
      simp only [componentSource,if_neg active]
      apply prepared_suffix_congr
      intro split splitMember afterSentinel
      have positive : 0 < before.componentStart key :=
        Nat.pos_of_ne_zero (fun zero => active ((PrefRouter.componentStart_zero_iff member).mp zero))
      have bounds := reference.node_bounds splitMember
      have unchanged := head_dormant_genuine_unchanged step distinct perfect member active memory split
        (by omega) (by omega)
      simpa only [ownerBits,step.searchPath] using unchanged
    simpa only [Function.update_of_ne active,sourceSame] using valid key member

end TangoSquared.Paper20261030.SecondaryDecomposition

namespace TangoSquared.Paper20261030.GlobalPrimaryRepresentation

open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection Secondary SecondaryDecomposition

variable {α η : Type*} [DecidableEq α] [DecidableEq η]

theorem LogicalInvariant.prepared_active_output {height d : Nat} (reference : DepthTree 0 height)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x d before after)
    (perfect : before.Perfect height) (distinct : before.leaves.Nodup) (memory : MemoryKey → Bool)
    (data : α → ComponentData α η) (valid : LogicalInvariant reference before perfect memory data)
    (fresh : ComponentData α η)
    (represented : Represents followsRight
      (source reference (intervalUpdate d (ownerBits before before.terminal memory))) fresh.component)
    (ids : fresh.decorated.inventory Prod.fst = (data before.terminal).decorated.inventory Prod.fst) :
    LogicalInvariant reference before perfect (advanceDepth before x d memory)
      (Function.update data before.terminal fresh) := by
  constructor
  · rw [components_update]
    exact valid.represented.prepared_active_output reference step perfect distinct memory (components data)
      fresh.component represented
  · have same : inventories (Function.update data before.terminal fresh) = inventories data := by
      funext key
      by_cases active : key = before.terminal
      · subst key; simpa only [inventories,Function.update_self] using ids
      · simp only [inventories,Function.update_of_ne active]
    rw [same]
    exact valid.unique

end TangoSquared.Paper20261030.GlobalPrimaryRepresentation
