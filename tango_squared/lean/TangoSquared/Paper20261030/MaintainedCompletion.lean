import TangoSquared.Paper20261030.MaintainedHeadLoop

/-!
# Completion access and original-key service

After the primary head loop the requested key is the active endpoint.
Accessing the completion depth changes only that endpoint's secondary
component. The complete component invariant remains valid, and a charged
visit reaches the original key stored at its physical bottom vertex.
-/

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem ownerBits_terminal_advance (primary : PrefRouter α) (memory : MemoryKey → Bool) (depth : Nat) :
    ownerBits primary primary.terminal (advanceDepth primary primary.terminal depth memory) =
      intervalUpdate depth (ownerBits primary primary.terminal memory) := by
  funext split
  simp only [ownerBits,advanceDepth,depthWrite,intervalUpdate,List.take_prefix,true_and]
  split_ifs <;> rfl

theorem terminal_dormant_genuine_unchanged {height : Nat} {primary : PrefRouter α}
    (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup)
    {key : α} (member : key ∈ primary.leaves) (other : key ≠ primary.terminal)
    (memory : MemoryKey → Bool) (depth : Nat) (split : DepthSplit)
    (below : primary.componentStart key ≤ split.lo) (upper : split.lo ≤ height) :
    ownerBits primary key (advanceDepth primary primary.terminal depth memory) split =
      ownerBits primary key memory split := by
  have addressLength : ((primary.searchPath key).take split.lo).length = split.lo := by
    rw [List.length_take,PrefRouter.searchPath_length perfect member,Nat.min_eq_left upper]
  have separate := PrefRouter.componentStart_owner_ne distinct member other below
  have outside : ¬ ((primary.searchPath key).take split.lo).IsPrefix (primary.searchPath primary.terminal) := by
    simpa only [List.prefix_iff_eq_take,addressLength] using separate
  simp [ownerBits,advanceDepth,depthWrite,outside]

end TangoSquared.Paper20261030.Secondary

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open ColoredStorage AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection PrimaryWings PackedPrimary Secondary SourcePointer

variable {α : Type*} [DecidableEq α]

theorem Components.Valid.terminal_access {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup)
    (memory : MemoryKey → Bool) (components : Components α)
    (valid : Components.Valid reference primary perfect memory components) (depth : Nat)
    (fresh : AuxiliaryComponent Nat Nat (Tagged Payload))
    (freshRep : Represents followsRight (source reference (intervalUpdate depth (ownerBits primary primary.terminal memory))) fresh) :
    Components.Valid reference primary perfect (advanceDepth primary primary.terminal depth memory)
      (Function.update components primary.terminal fresh) := by
  intro key member
  by_cases active : key = primary.terminal
  · subst key
    simpa only [componentSource_active,ownerBits_terminal_advance,Function.update_self] using freshRep
  · have sourceSame : componentSource reference primary perfect (advanceDepth primary primary.terminal depth memory) key =
        componentSource reference primary perfect memory key := by
      simp only [componentSource,if_neg active]
      apply prepared_suffix_congr
      intro split splitMember afterSentinel
      have positive : 0 < primary.componentStart key :=
        Nat.pos_of_ne_zero (fun zero => active ((PrefRouter.componentStart_zero_iff member).mp zero))
      have bounds := reference.node_bounds splitMember
      exact terminal_dormant_genuine_unchanged perfect distinct member active memory depth split (by omega) (by omega)
    simpa only [Function.update_of_ne active,sourceSame] using valid key member

theorem maintained_completion {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup)
    (memory : MemoryKey → Bool) (components : Components α)
    (valid : Components.Valid reference primary perfect memory components) :
    ∃ out : Components α,
      Components.Valid reference primary perfect (advanceDepth primary primary.terminal height memory) out ∧
      VisitsLeaf primary.terminal (physicalState primary components) (physicalState primary out)
        (((decodeDepth reference (ownerBits primary primary.terminal memory)).accessFlips height+1) *
          (1340000*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+20500)+5) := by
  obtain ⟨fresh,freshRep,accessTrace⟩ := maintained_physical_access reference primary perfect distinct
    memory components valid height (Nat.le_refl _)
  let out := Function.update components primary.terminal fresh
  have outValid := valid.terminal_access reference primary perfect distinct memory components height fresh freshRep
  have inputValid := outValid.input reference perfect distinct _ out ComponentRoot.root
  simp only [PrefRouter.componentStart_terminal] at inputValid
  have view := physicalState_as_input primary out inputValid
  have visit := physical_endpoint_visit (Input.mk 0 (closed (out primary.terminal)) inputValid)
    (storedPayload primary.componentStart out)
  rw [← view] at visit
  exact ⟨out,outValid,visit.prepend accessTrace⟩

end TangoSquared.Paper20261030.SecondaryDecomposition
