import ChaCha.Paper20261030.SplayAuxiliaryHeadLoop
import ChaCha.Paper20261030.CompletedDepthAccounting

/-! The final secondary access keeps the requested primary endpoint and
all dormant component inventories. Its ordinary-splay certificate is
part of the eventual request execution. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality.SearchRotation
open ColoredStorage PreferredProjection Secondary SecondaryDecomposition

variable {α : Type*} [DecidableEq α]

theorem Global.Table.Valid.terminal_access {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup)
    (memory : MemoryKey → Bool) (components : Global.Table α)
    (valid : Global.Table.Valid reference primary perfect memory components) (depth : Nat)
    (fresh : Global.Component)
    (freshValid : fresh.Valid (source reference (intervalUpdate depth (ownerBits primary primary.terminal memory)))) :
    Global.Table.Valid reference primary perfect (advanceDepth primary primary.terminal depth memory)
      (Function.update components primary.terminal fresh) := by
  intro key member
  by_cases active : key = primary.terminal
  · subst key
    simpa only [componentSource_active,ownerBits_terminal_advance,Function.update_self] using freshValid
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

inductive CompletionExecution {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (memory : MemoryKey → Bool) (components : Global.Table α) : Global.Table α → Prop
  | run {fresh : Global.Component} {work : Nat}
      (ordinary : SecondaryExecution reference height
        (decodeDepth reference (ownerBits primary primary.terminal memory))
        (decodeDepth reference (intervalUpdate height (ownerBits primary primary.terminal memory)))
        (referenceCuts id (components primary.terminal).auxiliary.closed)
        (referenceCuts id fresh.auxiliary.closed) work) :
      CompletionExecution reference primary memory components (Function.update components primary.terminal fresh)

theorem completion_exists {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup)
    (memory : MemoryKey → Bool) (components : Global.Table α)
    (valid : Global.Table.Valid reference primary perfect memory components) :
    ∃ (out : Global.Table α) (rotations : Nat),
      Global.Table.Valid reference primary perfect (advanceDepth primary primary.terminal height memory) out ∧
      Rotations (GapBST.encode (Physical.physicalState primary components))
        (GapBST.encode (Physical.physicalState primary out)) rotations ∧
      CompletionExecution reference primary memory components out ∧
      rotations+408*out.potential primary.leaves.toFinset ≤
        408*components.potential primary.leaves.toFinset+
          (decodeDepth reference (ownerBits primary primary.terminal memory)).accessFlips height * headFactor reference := by
  obtain ⟨fresh,work,freshValid,sourceRotations,ordinary,localBound⟩ :=
    component_access reference (ownerBits primary primary.terminal memory) height (components primary.terminal) valid.active
  let out : Global.Table α := Function.update components primary.terminal fresh
  have outValid := valid.terminal_access reference primary perfect distinct memory components height fresh freshValid
  obtain ⟨rotations,physical,bound⟩ := Physical.maintained_secondary_rotations reference
    (ownerBits primary primary.terminal memory) (intervalUpdate height (ownerBits primary primary.terminal memory))
    primary perfect distinct components fresh valid.active.1 freshValid.1 sourceRotations
  have globalBound := Global.Table.single_amortized primary.leaves.toFinset components primary.terminal
    (List.mem_toFinset.mpr primary.terminal_mem) fresh localBound
  refine ⟨out,rotations,outValid,physical,.run ordinary,?_⟩
  change work+2*out.potential primary.leaves.toFinset ≤ _ at globalBound
  unfold headFactor
  nlinarith

end ChaCha.Paper20261030.SplayAuxiliary
