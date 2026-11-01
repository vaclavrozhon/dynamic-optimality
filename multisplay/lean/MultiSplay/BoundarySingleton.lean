import MultiSplay.RichJoinTopDown
import MultiSplay.JoinRootGeometry

/-!
# Existing root blocks at a common split

At the common pivot each side has one heap child. In any stable current lazy
history, the block containing that child is therefore a singleton. A growing
singleton has value three in doubled priorities; a shrinking singleton has
value one. This applies after arbitrary intervening operations.
-/

namespace MultiSplay.BoundarySingleton

open Splay.Lazy (State Block HeapView Element Side IsSegment)

variable {n : Nat}

theorem segment_singleton {α : Type*} {inside : List α} {child : α}
    (segment : IsSegment inside [child]) (member : child ∈ inside) : inside = [child] := by
  obtain ⟨front, back, equation⟩ := segment
  have length := congrArg List.length equation
  simp only [List.length_append, List.length_cons, List.length_nil] at length
  have positive : 0 < inside.length := List.length_pos_iff.mpr (List.ne_nil_of_mem member)
  obtain ⟨element, eq⟩ := List.length_eq_one_iff.mp (show inside.length = 1 by omega)
  rw [eq] at member ⊢
  simpa only [List.mem_singleton] using congrArg (fun x => [x]) (List.mem_singleton.mp member).symm

theorem block_singleton {params : Splay.Interface.Parameters} (state : State n)
    (stable : state.Stable params) (pivot child : Element n) (side : Side)
    (parent : state.view.parent child = some pivot) (childSide : state.view.side child = side)
    (children : state.view.topDown pivot side = [child]) (block : Block n)
    (blockMem : block ∈ state.blocks) (member : child ∈ block.elements) :
    block.owner = pivot ∧ block.side = side ∧ block.elements = [child] := by
  have valid := stable.valid.2 block blockMem
  have ownerEq : block.owner = pivot := Option.some.inj ((valid.parent_eq member).symm.trans parent)
  have sideEq : block.side = side := (valid.side_eq member).symm.trans childSide
  have segment := valid.1
  rw [RichJoin.complete_attached state stable.2.1, ownerEq, sideEq, children] at segment
  exact ⟨ownerEq, sideEq, segment_singleton segment member⟩

theorem shrinking_gap (view : HeapView n) (block : Block n) (child : Element n)
    (valid : block.GapValid view) (shrinking : block.mode = .shrinking) (singleton : block.elements = [child]) :
    block.intervalGap = view.rawGap child := by
  simp only [Block.GapValid, shrinking] at valid
  rcases valid with empty | nonempty
  · simp [singleton] at empty
  · obtain ⟨⟨witness, member, attained⟩, _⟩ := nonempty.2
    have same : witness = child := by simpa [singleton] using member
    simpa only [same] using attained.symm

theorem value_modes {params : Splay.Interface.Parameters} (state : State n)
    (stable : state.Stable params) (block : Block n) (child : Element n)
    (blockMem : block ∈ state.blocks) (singleton : block.elements = [child])
    (gap : state.view.rawGap child = 2) :
    (block.mode = .growing → state.value child = 3) ∧
      (block.mode = .shrinking → state.value child = 1) := by
  have valid := stable.valid.2 block blockMem
  have synced := stable.value_eq_transientContractedGap blockMem (show child ∈ block.elements by simp [singleton])
  constructor
  · intro growing
    rw [valid.growing_intervalGap_eq_zero growing, gap, JoinPriority.root_contracted] at synced
    exact synced
  · intro shrinking
    have interval := shrinking_gap state.view block child valid.2.2 shrinking singleton
    rw [interval, gap] at synced
    have neutral : Splay.Analysis.transientContractedGap 2 2 = 1 := by decide
    simpa only [neutral] using synced

theorem value_le_three {params : Splay.Interface.Parameters} (state : State n)
    (stable : state.Stable params) (pivot child : Element n) (side : Side)
    (parent : state.view.parent child = some pivot) (childSide : state.view.side child = side)
    (children : state.view.topDown pivot side = [child]) (gap : state.view.rawGap child = 2) :
    state.value child = 1 ∨ state.value child = 3 := by
  have member : child ∈ state.allElements := (stable.2.1 child).mpr (by rw [parent]; exact Option.some_ne_none _)
  obtain ⟨block, blockMem, elementMem⟩ := State.mem_allElements_iff.mp member
  have singleton := (block_singleton state stable pivot child side parent childSide children block blockMem elementMem).2.2
  have modes := value_modes state stable block child blockMem singleton gap
  cases modeEq : block.mode with
  | growing => exact Or.inr (modes.1 modeEq)
  | shrinking => exact Or.inl (modes.2 modeEq)

end MultiSplay.BoundarySingleton
