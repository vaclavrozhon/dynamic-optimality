import Splay.Lazy.CutCrossing

namespace Splay.Lazy

private theorem filter_partition_of_pairwise {α : Type*} {R : α → α → Prop}
    (predicate : α → Bool) (closed : ∀ a b, R a b → predicate b = true → predicate a = true)
    (elements : List α) (ordered : elements.Pairwise R) :
    elements = elements.filter predicate ++ elements.filter (fun element => !(predicate element)) := by
  induction elements with
  | nil => rfl
  | cons head tail ih =>
      have pairs := List.pairwise_cons.mp ordered
      cases headPasses : predicate head with
      | true => simpa [headPasses] using congrArg (head :: ·) (ih pairs.2)
      | false =>
          have tailRejects : ∀ element ∈ tail, predicate element = false := by
            intro element member
            cases selected : predicate element with
            | false => rfl
            | true => have impossible := closed head element (pairs.1 element member) selected; simp [headPasses] at impossible
          have empty : tail.filter predicate = [] := List.filter_eq_nil_iff.mpr
            (by intro element member; simp [tailRejects element member])
          have all : tail.filter (fun element => !(predicate element)) = tail :=
            List.filter_eq_self.mpr (by intro element member; simp [tailRejects element member])
          simp [headPasses, empty, all]

/-- Predicate for the prefix preceding a numerical cut in one side's
top-down child order. The right side is ordered decreasingly. -/
def cutPrefixPredicate {n : ℕ} (side : Side) (cut : ℕ) (element : Element n) : Bool :=
  match side with
  | .left => decide (element.val < cut)
  | .right => decide (cut ≤ element.val)

theorem cutPrefix_partition {n : ℕ} (elements : List (Element n)) (side : Side) (cut : ℕ)
    (ordered : elements.Pairwise (fun a b => match side with
      | .left => a.val < b.val | .right => b.val < a.val)) :
    elements = elements.filter (cutPrefixPredicate side cut) ++
      elements.filter (fun element => !(cutPrefixPredicate side cut element)) := by
  apply filter_partition_of_pairwise _ _ elements ordered
  intro a b relation passes
  cases side <;> simp only [cutPrefixPredicate, decide_eq_true_eq] at passes ⊢ <;> dsimp only at relation <;> omega

namespace Block

def cutPrefixLength {n : ℕ} (cut : ℕ) (block : Block n) : ℕ :=
  (block.elements.filter (cutPrefixPredicate block.side cut)).length

theorem cutPrefixLength_le {n : ℕ} (cut : ℕ) (block : Block n) :
    block.cutPrefixLength cut ≤ block.elements.length := List.length_filter_le _ _

theorem cut_take_drop {n : ℕ} (cut : ℕ) (block : Block n)
    (ordered : block.elements.Pairwise (fun a b => match block.side with
      | .left => a.val < b.val | .right => b.val < a.val)) :
    block.elements.take (block.cutPrefixLength cut) = block.elements.filter (cutPrefixPredicate block.side cut) ∧
      block.elements.drop (block.cutPrefixLength cut) = block.elements.filter (fun element => !(cutPrefixPredicate block.side cut element)) := by
  have partition := cutPrefix_partition block.elements block.side cut ordered
  have takeEq := congrArg (List.take (block.cutPrefixLength cut)) partition
  have dropEq := congrArg (List.drop (block.cutPrefixLength cut)) partition
  constructor
  · simpa only [cutPrefixLength, List.take_left] using takeEq
  · simpa only [cutPrefixLength, List.drop_left] using dropEq

/-- Both pieces of the actual rich split lie wholly on one side of the cut. -/
theorem cut_split_not_crosses {n : ℕ} (cut : ℕ) (block : Block n) (prefixGap suffixGap : ℤ)
    (ordered : block.elements.Pairwise (fun a b => match block.side with
      | .left => a.val < b.val | .right => b.val < a.val)) :
    ¬ (block.splitPrefix (block.cutPrefixLength cut) prefixGap).CrossesCut cut ∧
      ¬ (block.splitSuffix (block.cutPrefixLength cut) suffixGap).CrossesCut cut := by
  have pieces := block.cut_take_drop cut ordered
  constructor
  · rintro ⟨low, lowIn, high, highIn, lowBound, highBound⟩
    change low ∈ block.elements.take (block.cutPrefixLength cut) at lowIn
    change high ∈ block.elements.take (block.cutPrefixLength cut) at highIn
    rw [pieces.1] at lowIn highIn
    have lowPasses := (List.mem_filter.mp lowIn).2
    have highPasses := (List.mem_filter.mp highIn).2
    cases side : block.side <;> simp only [cutPrefixPredicate, side, decide_eq_true_eq] at lowPasses highPasses <;> omega
  · rintro ⟨low, lowIn, high, highIn, lowBound, highBound⟩
    change low ∈ block.elements.drop (block.cutPrefixLength cut) at lowIn
    change high ∈ block.elements.drop (block.cutPrefixLength cut) at highIn
    rw [pieces.2] at lowIn highIn
    have lowFails := (List.mem_filter.mp lowIn).2
    have highFails := (List.mem_filter.mp highIn).2
    change Bool.not (cutPrefixPredicate block.side cut low) = true at lowFails
    change Bool.not (cutPrefixPredicate block.side cut high) = true at highFails
    cases side : block.side <;> simp [cutPrefixPredicate, side] at lowFails highFails <;> omega

end Block
end Splay.Lazy
