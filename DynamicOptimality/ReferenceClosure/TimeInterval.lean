import DynamicOptimality.ReferenceClosure.Cardinality
import DynamicOptimality.ReferenceClosure.Crossing

/-!+# Closure over a closed time interval

If every row is NCA-closed and the whole finite point set is arborally
satisfied, the union of the keys in any closed time interval is NCA-closed.
The resulting pivot witness may occur anywhere in that interval; the
statement does not move the pivot to a later request's time.
-/

namespace DynamicOptimality.Geometry.ReferenceClosure

open Splay.Tree

def intervalKeys (points : Finset Point) (start finish : Int) : Finset Nat :=
  (points.filter fun p => start ≤ p.2 ∧ p.2 ≤ finish).image Prod.fst

@[simp] theorem mem_intervalKeys {points : Finset Point} {start finish : Int} {key : Nat} :
    key ∈ intervalKeys points start finish ↔
      ∃ time, (key,time) ∈ points ∧ start ≤ time ∧ time ≤ finish := by
  simp only [intervalKeys, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨k,t⟩, ⟨member, lower, upper⟩, rfl⟩
    exact ⟨t, member, lower, upper⟩
  · rintro ⟨t, member, lower, upper⟩
    exact ⟨(key,t), ⟨member, lower, upper⟩, rfl⟩

private theorem pivot_in_interval {lo pivot hi : Nat} (left : BST lo pivot)
    (right : BST (pivot+1) hi) {points : Finset Point}
    (satisfied : ArborallySatisfied points)
    (closed : ∀ time, row (.node left right) (rowAt points time) ⊆ rowAt points time)
    {start finish : Int} {a b : Nat}
    (ha : a ∈ intervalKeys points start finish) (hb : b ∈ intervalKeys points start finish)
    (al : lo ≤ a) (ar : a < pivot) (bl : pivot < b) (br : b < hi) :
    pivot ∈ intervalKeys points start finish := by
  classical
  obtain ⟨ta, ha, taLow, taHigh⟩ := mem_intervalKeys.mp ha
  obtain ⟨tb, hb, tbLow, tbHigh⟩ := mem_intervalKeys.mp hb
  let box := points.filter fun p => p.1 ∈ Set.Ico lo hi ∧ p.2 ∈ Set.Icc start finish
  have boxSatisfied : Satisfied box := by
    have keyConvex : ConvexKeys (Set.Ico lo hi) := by
      intro x hx y hy z lower upper
      exact ⟨hx.1.trans lower, upper.trans_lt hy.2⟩
    have timeConvex : ConvexKeys (Set.Icc start finish) := by
      intro x hx y hy z lower upper
      exact ⟨hx.1.trans lower, upper.trans hy.2⟩
    convert ((satisfied_iff points).mpr satisfied).restrict keyConvex timeConvex using 1
    ext p
    simp only [box, Finset.mem_filter]
  have haBox : (a,ta) ∈ box := Finset.mem_filter.mpr ⟨ha, ⟨al, ar.trans bl |>.trans br⟩,
    taLow, taHigh⟩
  have hbBox : (b,tb) ∈ box := Finset.mem_filter.mpr ⟨hb, ⟨al.trans ar.le |>.trans bl.le, br⟩,
    tbLow, tbHigh⟩
  rcases boxSatisfied.crossing haBox hbBox ar bl with ⟨p, hp, eq⟩ | ⟨time, straddles⟩
  · obtain ⟨old, _, bounds⟩ := Finset.mem_filter.mp hp
    exact mem_intervalKeys.mpr ⟨p.2, by simpa [← eq] using old, bounds⟩
  · obtain ⟨p, hp, q, hq, pt, qt, _, _, pl, qr⟩ := straddles
    obtain ⟨oldP, pk, timeP⟩ := Finset.mem_filter.mp hp
    obtain ⟨oldQ, qk, _⟩ := Finset.mem_filter.mp hq
    have pRow : p.1 ∈ rowAt points time := mem_rowAt.mpr (by simpa [← pt] using oldP)
    have qRow : q.1 ∈ rowAt points time := mem_rowAt.mpr (by simpa [← qt] using oldQ)
    have inLeft : p.1 ∈ row left (rowAt points time) := selected_subset_row left _
      ((mem_selected left _).mpr ⟨pRow, pk.1, pl⟩)
    have inRight : q.1 ∈ row right (rowAt points time) := selected_subset_row right _
      ((mem_selected right _).mpr ⟨qRow, by omega, qk.2⟩)
    have pivotRow : pivot ∈ row (.node left right) (rowAt points time) := by
      have nl : (row left (rowAt points time)).Nonempty := ⟨p.1, inLeft⟩
      have nr : (row right (rowAt points time)).Nonempty := ⟨q.1, inRight⟩
      simp [row, nl, nr]
    exact mem_intervalKeys.mpr ⟨time, mem_rowAt.mp (closed time pivotRow),
      by simpa [pt] using timeP.1, by simpa [pt] using timeP.2⟩

theorem nca_mem_intervalKeys {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (satisfied : ArborallySatisfied points)
    (closed : ∀ time, row tree (rowAt points time) ⊆ rowAt points time)
    {start finish : Int} {a b : Nat}
    (ha : a ∈ intervalKeys points start finish) (hb : b ∈ intervalKeys points start finish)
    (aBounds : lo ≤ a ∧ a < hi) (bBounds : lo ≤ b ∧ b < hi) :
    nca tree a b ∈ intervalKeys points start finish := by
  induction tree with
  | empty => omega
  | @node lo pivot hi left right ihl ihr =>
    have closedLeft : ∀ time, row left (rowAt points time) ⊆ rowAt points time := by
      intro time key member
      exact closed time (Finset.mem_union_left _ (Finset.mem_union_left _ member))
    have closedRight : ∀ time, row right (rowAt points time) ⊆ rowAt points time := by
      intro time key member
      exact closed time (Finset.mem_union_left _ (Finset.mem_union_right _ member))
    by_cases bothLeft : a < pivot ∧ b < pivot
    · simp only [nca, if_pos bothLeft]
      exact ihl closedLeft ⟨aBounds.1, bothLeft.1⟩ ⟨bBounds.1, bothLeft.2⟩
    · by_cases bothRight : pivot < a ∧ pivot < b
      · simp only [nca, if_neg bothLeft, if_pos bothRight]
        exact ihr closedRight ⟨by omega, aBounds.2⟩ ⟨by omega, bBounds.2⟩
      · simp only [nca, if_neg bothLeft, if_neg bothRight]
        by_cases aRoot : a = pivot
        · simpa [aRoot] using ha
        · by_cases bRoot : b = pivot
          · simpa [bRoot] using hb
          · have mixed : (a < pivot ∧ pivot < b) ∨ (b < pivot ∧ pivot < a) := by omega
            rcases mixed with ⟨al, br⟩ | ⟨bl, ar⟩
            · exact pivot_in_interval left right satisfied closed ha hb aBounds.1 al br bBounds.2
            · exact pivot_in_interval left right satisfied closed hb ha bBounds.1 bl ar aBounds.2

theorem intervalKeys_closed {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (satisfied : ArborallySatisfied points)
    (closed : ∀ time, row tree (rowAt points time) ⊆ rowAt points time)
    (bounded : ∀ p ∈ points, lo ≤ p.1 ∧ p.1 < hi) (start finish : Int) :
    row tree (intervalKeys points start finish) = intervalKeys points start finish := by
  have intervalBound : ∀ key ∈ intervalKeys points start finish, lo ≤ key ∧ key < hi := by
    intro key member
    obtain ⟨time, old, _⟩ := mem_intervalKeys.mp member
    exact bounded (key,time) old
  apply Finset.Subset.antisymm
  · intro key member
    rcases (mem_row_iff tree _).mp member with old | ⟨a, ha, b, hb, rfl⟩
    · exact ((mem_selected tree _).mp old).1
    · obtain ⟨ha, aBounds⟩ := (mem_selected tree _).mp ha
      obtain ⟨hb, bBounds⟩ := (mem_selected tree _).mp hb
      exact nca_mem_intervalKeys tree satisfied closed ha hb aBounds bBounds
  · intro key member
    exact selected_subset_row tree _ ((mem_selected tree _).mpr ⟨member, intervalBound key member⟩)

/-- The interval-closure conclusion for the actual constructed point set. -/
theorem closePoints_interval_closed {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (satisfied : ArborallySatisfied points)
    (bounded : ∀ p ∈ points, lo ≤ p.1 ∧ p.1 < hi) (start finish : Int) :
    row tree (intervalKeys (closePoints tree points) start finish) =
      intervalKeys (closePoints tree points) start finish :=
  intervalKeys_closed tree (closePoints_satisfied tree satisfied)
    (fun time => (closed_rows tree bounded time).subset)
    (closePoints_bounded tree bounded) start finish

end DynamicOptimality.Geometry.ReferenceClosure
