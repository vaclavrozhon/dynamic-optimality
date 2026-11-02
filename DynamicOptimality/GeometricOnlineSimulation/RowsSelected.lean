import DynamicOptimality.GeometricOnlineSimulation.RowsExtract
import DynamicOptimality.GeometricOnlineSimulation.ClassProperties
import DynamicOptimality.GeometricModel

/-! # The selected skeleton and its new last-touch class -/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR

namespace ClassFrame.Selected

theorem mem_iff {system : SplitTreeSystem} {height : Nat → Int} {row : Finset Nat}
    {lower upper : Nat} {skeleton : RawTree Nat} {frame : ClassFrame system skeleton}
    (selected : frame.Selected height row lower upper) (key : Nat) :
    key ∈ skeleton.inorder ↔ lower ≤ key ∧ key < upper ∧ key ∈ row := by
  constructor
  · exact selected.key_bounds key
  · intro ⟨lo, hi, member⟩
    induction skeleton generalizing lower upper with
    | empty =>
        cases frame with
        | hole child =>
            cases selected with
            | hole property => exact False.elim (property.2 key lo hi member)
    | node left root right ihl ihr =>
        cases frame with
        | node front _ back =>
            cases selected with
            | node rootLo rootHi first last rootMember =>
                simp only [Tree.inorder, List.mem_append, List.mem_singleton]
                rcases lt_trichotomy key root with before | rfl | after
                · exact Or.inl (Or.inl (ihl first lo before))
                · exact Or.inl (Or.inr rfl)
                · exact Or.inr (ihr last (by omega) hi)

theorem size_le {system : SplitTreeSystem} {height : Nat → Int} {row : Finset Nat}
    {lower upper : Nat} {skeleton : RawTree Nat} {frame : ClassFrame system skeleton}
    (selected : frame.Selected height row lower upper) : skeleton.size ≤ row.card := by
  classical
  have subset : skeleton.inorder.toFinset ⊆ row := by
    intro key member
    exact ((selected.mem_iff key).mp (List.mem_toFinset.mp member)).2.2
  have bound := Finset.card_le_card subset
  rw [List.toFinset_card_of_nodup selected.ordered_skeleton.nodup,
    Tree.length_inorder] at bound
  exact bound

theorem retime {system : SplitTreeSystem} {height : Nat → Int} {row : Finset Nat}
    {time : Int} {lower upper : Nat} {skeleton : RawTree Nat}
    {frame : ClassFrame system skeleton}
    (selected : frame.Selected height row lower upper)
    (fresh : ∀ key, lower ≤ key → key < upper → height key < time) :
    frame.Realizes (Geometry.update height time row) time lower upper := by
  induction skeleton generalizing lower upper with
  | empty =>
      cases frame with
      | hole child =>
          cases selected with
          | hole property =>
              refine .hole (property.1.congr ?_) ?_
              · intro key lo hi
                simp only [Geometry.update, if_neg (property.2 key lo hi)]
              · intro key lo hi
                simpa only [Geometry.update, if_neg (property.2 key lo hi)] using fresh key lo hi
  | node left root right ihl ihr =>
      cases frame with
      | node front _ back =>
          cases selected with
          | node rootLo rootHi first last member =>
              refine .node rootLo rootHi (ihl first ?_) (ihr last ?_) ?_
              · intro key lo hi
                exact fresh key lo (by omega)
              · intro key lo hi
                exact fresh key (by omega) hi
              · simp only [Geometry.update, if_pos member]

end ClassFrame.Selected

end DynamicOptimality.GeometricOnlineSimulation
