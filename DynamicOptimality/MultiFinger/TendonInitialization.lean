import DynamicOptimality.MultiFinger.TendonContents

/-! Linear initial imbalance for exact source tendons.
The queue construction uses each original suppressed vertex once and
retains its literal hanging subtree. No balanced-tree complexity premise
is included in this initialization. -/

namespace DynamicOptimality.MultiFinger.TendonContents

open ChaCha.MTR SingleFinger
open DynamicOptimality.GeometricOnlineSimulation.OpenDeque
open TendonSource

variable {α : Type*}

theorem firstGap_append_singleton (cells : List (LowCell α)) (gap inside : RawTree α) (key : α) :
    firstGap (cells++[(gap,key)]) inside = firstGap cells gap := by cases cells <;> rfl

theorem afterCells_append_singleton (cells : List (LowCell α)) (gap inside : RawTree α) (key : α) :
    afterCells (cells++[(gap,key)]) inside = afterCells cells gap++[(key,inside)] := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    cases cell
    simp only [List.cons_append,afterCells,firstGap_append_singleton,ih]

theorem LowValid.append {layout : Right α} {cells : List (LowCell α)}
    (valid : LowValid layout cells) (gap : RawTree α) (key : α) :
    LowValid (layout.append gap key) (cells++[(gap,key)]) := by
  intro inside
  rw [Right.append_fill]
  constructor
  · simpa only [SingleFinger.Deque.pushMaxLayout,firstGap_append_singleton] using (valid gap).1
  · simpa only [SingleFinger.Deque.pushMaxLayout,SingleFinger.Deque.Layout.cells,
      List.append_assoc,List.cons_append,afterCells_append_singleton] using
      congrArg (fun entries => entries++[(key,inside)]) (valid gap).2

theorem low_initialization (cells : List (LowCell α)) :
    ∃ layout : Option (Right α), LowRep layout cells ∧
      (layout.map Right.potential).getD 0 ≤ 4*cells.length := by
  induction cells using List.reverseRecOn with
  | nil => exact ⟨none,rfl,by simp⟩
  | append_singleton cells cell ih =>
    rcases cell with ⟨gap,key⟩
    obtain ⟨layout,valid,paid⟩ := ih
    cases layout with
    | none =>
      change cells = [] at valid
      subst cells
      refine ⟨some ⟨gap,[],key,none⟩,?_,?_⟩
      · intro inside
        exact ⟨rfl,rfl⟩
      · simp [Right.potential,Right.fill,SingleFinger.Deque.Layout.potential,SingleFinger.Deque.potential]
    | some queue =>
      refine ⟨some (queue.append gap key),LowValid.append valid gap key,?_⟩
      have bound := queue.append_potential gap key
      simp only [Option.map_some,Option.getD_some,List.length_append,List.length_cons,List.length_nil] at paid ⊢
      omega

theorem high_initialization (cells : List (HighCell α)) :
    ∃ layout : Option (Left α), HighRep layout cells ∧
      (layout.map Left.potential).getD 0 ≤ 4*cells.length := by
  cases cells with
  | nil => exact ⟨none,rfl,by simp⟩
  | cons cell cells =>
    rcases cell with ⟨key,gap⟩
    refine ⟨some ⟨[],key,gap,cells⟩,?_,?_⟩
    · intro inside
      rfl
    · simp [Left.potential,Left.fill,SingleFinger.Deque.Layout.potential,SingleFinger.Deque.potential]

theorem initialization (source : List (Pointer.Frame α)) :
    ∃ tendon : Tendon α, tendon.Represents source ∧ tendon.potential ≤ 4*source.length := by
  obtain ⟨lower,lowerRep,lowerPaid⟩ := low_initialization (low source)
  obtain ⟨upper,upperRep,upperPaid⟩ := high_initialization (high source)
  refine ⟨⟨lower,upper⟩,⟨lowerRep,upperRep⟩,?_⟩
  have count := side_count source
  simp only [Tendon.potential]
  omega

end DynamicOptimality.MultiFinger.TendonContents
