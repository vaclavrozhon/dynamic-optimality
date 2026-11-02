import ChaCha.Paper20261030.SecondaryReference

/-!
# The actual induced depth reference of a classical path component

`suffix reference start` retains exactly the depth leaves from `start` to
the original upper endpoint. It suppresses unary vertices and reuses the
existing `DepthTree` type. An interval crossing `start` has its lower
endpoint clipped, but its separator key still identifies the unique
original interval. This distinction lets later comparator accesses keep
genuine owner histories separate from the structural boundary spine.
-/

namespace MultiSplay.ComparatorSuffix

open ChaCha
open ChaCha.Paper20261030.LocalReferences (depthReference)

def suffix : {a b : Nat} → DepthTree a b →
    (start : Nat) → a ≤ start → start ≤ b → DepthTree start b
  | _, _, .leaf a, start, lower, upper => by
      have same : start = a := by omega
      subst start
      exact .leaf a
  | _, _, .node cut _ upper left right, start, lower, bound =>
      if retained : start ≤ cut then
        .node cut retained upper (suffix left start lower retained) right
      else suffix right start (by omega) bound

theorem suffix_height {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lower : a ≤ start) (upper : start ≤ b) :
    (depthReference (suffix reference start lower upper)).height ≤
      (depthReference reference).height := by
  induction reference with
  | leaf a =>
      have same : start = a := by omega
      subst start
      exact le_rfl
  | @node a b cut ha hb left right ihl ihr =>
      by_cases retained : start ≤ cut
      · have bound := ihl lower retained
        simp only [suffix, dif_pos retained, depthReference, RouterProjection.Router.height]
        omega
      · have bound := ihr (by omega) upper
        simp only [suffix, dif_neg retained, depthReference, RouterProjection.Router.height]
        omega

@[simp] theorem suffix_minimum {a b : Nat} (reference : DepthTree a b)
    (upper : a ≤ b) : suffix reference a le_rfl upper = reference := by
  induction reference with
  | leaf => rfl
  | node cut ha hb left right ihl ihr =>
      simp only [suffix, dif_pos ha, ihl]

/-- The induced reference has exactly the intended depth alphabet. -/
theorem suffix_leaves {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lower : a ≤ start) (upper : start ≤ b) :
    (depthReference (suffix reference start lower upper)).leaves =
      List.range' start (b + 1 - start) :=
  Paper20261030.LocalReferences.depthReference_leaves _

def clip (start : Nat) (split : DepthSplit) : DepthSplit :=
  ⟨max start split.lo, split.cut, split.hi⟩

@[simp] theorem clip_cut (start : Nat) (split : DepthSplit) :
    (clip start split).cut = split.cut := rfl

theorem clip_genuine (start : Nat) (split : DepthSplit) (genuine : start ≤ split.lo) :
    clip start split = split := by
  cases split
  simp only [clip, max_eq_right genuine]

/-- Every retained separator has exactly its original upper endpoint and
cut; only a crossing interval's lower endpoint can change. -/
theorem suffix_node_original {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lower : a ≤ start) (upper : start ≤ b)
    {split : DepthSplit} (member : split ∈ (suffix reference start lower upper).nodes) :
    ∃ original ∈ reference.nodes, start ≤ original.cut ∧ clip start original = split := by
  induction reference with
  | leaf a =>
      have same : start = a := by omega
      subst start
      simp only [suffix, DepthTree.nodes, Finset.notMem_empty] at member
  | @node a b cut ha hb left right ihl ihr =>
      by_cases retained : start ≤ cut
      · simp only [suffix, dif_pos retained, DepthTree.nodes, Finset.mem_insert,
          Finset.mem_union] at member
        rcases member with rfl | inLeft | inRight
        · exact ⟨⟨a, cut, b⟩, by simp [DepthTree.nodes], retained, by
            simp only [clip, max_eq_left lower]⟩
        · obtain ⟨original, present, bound, same⟩ := ihl lower retained inLeft
          exact ⟨original, by simp [DepthTree.nodes, present], bound, same⟩
        · have bounds := right.node_bounds inRight
          refine ⟨split, by simp [DepthTree.nodes, inRight], by omega, ?_⟩
          exact clip_genuine start split (by omega)
      · simp only [suffix, dif_neg retained] at member
        obtain ⟨original, present, bound, same⟩ := ihr (by omega) upper member
        exact ⟨original, by simp [DepthTree.nodes, present], bound, same⟩

/-- No original interval with a retained separator is lost. In particular,
every genuine interval survives with its original identity. -/
theorem original_node_suffix {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lower : a ≤ start) (upper : start ≤ b)
    {original : DepthSplit} (member : original ∈ reference.nodes)
    (retained : start ≤ original.cut) :
    clip start original ∈ (suffix reference start lower upper).nodes := by
  induction reference with
  | leaf a => simp only [DepthTree.nodes, Finset.notMem_empty] at member
  | @node a b cut ha hb left right ihl ihr =>
      by_cases keptRoot : start ≤ cut
      · simp only [suffix, dif_pos keptRoot, DepthTree.nodes, Finset.mem_insert, Finset.mem_union]
        simp only [DepthTree.nodes, Finset.mem_insert, Finset.mem_union] at member
        rcases member with rfl | inLeft | inRight
        · exact Or.inl (by simp only [clip, max_eq_left lower])
        · exact Or.inr (Or.inl (ihl lower keptRoot inLeft))
        · have bounds := right.node_bounds inRight
          exact Or.inr (Or.inr ((clip_genuine start original (by omega)).symm ▸ inRight))
      · simp only [suffix, dif_neg keptRoot]
        simp only [DepthTree.nodes, Finset.mem_insert, Finset.mem_union] at member
        rcases member with rfl | inLeft | inRight
        · exact False.elim (keptRoot retained)
        · have bounds := left.node_bounds inLeft
          omega
        · exact ihr (by omega) upper inRight

/-- Genuine records are retained literally, without being reindexed. -/
theorem genuine_node_suffix {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lower : a ≤ start) (upper : start ≤ b)
    {original : DepthSplit} (member : original ∈ reference.nodes)
    (genuine : start ≤ original.lo) :
    original ∈ (suffix reference start lower upper).nodes := by
  have bounds := reference.node_bounds member
  simpa only [clip_genuine start original genuine] using
    original_node_suffix reference start lower upper member (by omega)

/-- A separator key, unlike a clipped lower endpoint, uniquely determines
the persistent original reference record. -/
theorem original_of_cut {a b : Nat} (reference : DepthTree a b)
    {split : DepthSplit} (member : split ∈ reference.nodes) :
    reference.locate split.cut (split.cut + 1) = some split := by
  have bounds := reference.node_bounds member
  exact reference.locate_of_separates member ⟨bounds.2.1, le_rfl, by omega, by omega⟩

theorem original_cut_unique {a b : Nat} (reference : DepthTree a b)
    {first second : DepthSplit} (firstMember : first ∈ reference.nodes)
    (secondMember : second ∈ reference.nodes) (same : first.cut = second.cut) : first = second := by
  have one := original_of_cut reference firstMember
  have two := original_of_cut reference secondMember
  rw [same] at one
  exact Option.some.inj (one.symm.trans two)

theorem suffix_original_lookup {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lower : a ≤ start) (upper : start ≤ b)
    {split : DepthSplit} (member : split ∈ (suffix reference start lower upper).nodes) :
    ∃ original ∈ reference.nodes,
      reference.locate split.cut (split.cut + 1) = some original ∧
      clip start original = split := by
  obtain ⟨original, present, _, same⟩ := suffix_node_original reference start lower upper member
  refine ⟨original, present, ?_, same⟩
  have cuts : original.cut = split.cut := by
    simpa only [clip_cut] using congrArg DepthSplit.cut same
  simpa only [cuts] using original_of_cut reference present

end MultiSplay.ComparatorSuffix
