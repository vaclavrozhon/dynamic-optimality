import MultiSplay.SplayDeterminism
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-!
# The access lemma for the actual bottom-up auxiliary splays

The potential uses twice the sum of the integer binary subtree ranks.
Integer ranks avoid analytic assumptions: two disjoint nonempty subtrees
cannot both have the same binary rank as their containing subtree.
The execution relation is the existing `MultiSplay.Auxiliary.Splay`, whose
index is the exact number of ordinary rotations.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder size rootKey)
open MultiSplay.Auxiliary

variable {α : Type*}

def rank (tree : RawTree α) : Nat := Nat.log 2 (size tree)

def potential : RawTree α → Nat
  | .empty => 0
  | .node left key right => potential left + potential right + rank (.node left key right)

theorem rank_mono {a b : RawTree α} (bound : size a ≤ size b) : rank a ≤ rank b :=
  Nat.log_mono_right bound

/-- Disjoint positive sizes force a strict rank loss in at least one part. -/
theorem disjoint_ranks {a b total : Nat} (positiveA : 0 < a) (positiveB : 0 < b)
    (disjoint : a+b ≤ total) : Nat.log 2 a + Nat.log 2 b + 1 ≤ 2*Nat.log 2 total := by
  have left := Nat.log_mono_right (show a ≤ total by omega) (b := 2)
  have right := Nat.log_mono_right (show b ≤ total by omega) (b := 2)
  by_contra failed
  have sameA : Nat.log 2 a = Nat.log 2 total := by omega
  have sameB : Nat.log 2 b = Nat.log 2 total := by omega
  have powA := Nat.pow_log_le_self 2 (Nat.ne_of_gt positiveA)
  have powB := Nat.pow_log_le_self 2 (Nat.ne_of_gt positiveB)
  have upper := Nat.lt_pow_succ_log_self (by decide : 1 < 2) total
  rw [sameA] at powA
  rw [sameB] at powB
  simp only [Nat.pow_succ] at upper
  omega

theorem potential_le (tree : RawTree α) (capacity : Nat) (bounded : size tree ≤ capacity) :
    potential tree ≤ size tree * Nat.log 2 capacity := by
  induction tree with
  | empty => simp [potential,size]
  | node left key right ihl ihr =>
      have left := ihl (by simp only [size] at bounded; omega)
      have right := ihr (by simp only [size] at bounded; omega)
      have root := Nat.log_mono_right bounded (b := 2)
      simp only [potential,rank,size] at *
      nlinarith

section KeyRank

variable [DecidableEq α]

/-- The rank of the uniquely occurring accessed key. -/
def keyRank (key : α) : RawTree α → Nat
  | .empty => 0
  | .node left pivot right =>
      if key = pivot then rank (.node left pivot right) else keyRank key left + keyRank key right

@[simp] theorem keyRank_root (left right : RawTree α) (key : α) :
    keyRank key (.node left key right) = rank (.node left key right) := by simp [keyRank]

theorem keyRank_absent {key : α} {tree : RawTree α} (absent : key ∉ inorder tree) :
    keyRank key tree = 0 := by
  induction tree with
  | empty => rfl
  | node left pivot right ihl ihr =>
      have different : key ≠ pivot := by intro same; subst pivot; exact absent (by simp [inorder])
      have left : key ∉ inorder left := fun h => absent (by simp [inorder,h])
      have right : key ∉ inorder right := fun h => absent (by simp [inorder,h])
      simp [keyRank,different,ihl left,ihr right]

theorem keyRank_left {key pivot : α} {left right : RawTree α}
    (unique : (inorder (.node left pivot right)).Nodup) (present : key ∈ inorder left) :
    keyRank key (.node left pivot right) = keyRank key left := by
  have parts := nodup_node unique
  have different : key ≠ pivot := by intro same; subst pivot; exact parts.2.2.1 present
  have absent : key ∉ inorder right := fun h => List.disjoint_left.mp parts.2.2.2.2 present h
  simp [keyRank,different,keyRank_absent absent]

theorem keyRank_right {key pivot : α} {left right : RawTree α}
    (unique : (inorder (.node left pivot right)).Nodup) (present : key ∈ inorder right) :
    keyRank key (.node left pivot right) = keyRank key right := by
  have parts := nodup_node unique
  have different : key ≠ pivot := by intro same; subst pivot; exact parts.2.2.2.1 present
  have absent : key ∉ inorder left := fun h => List.disjoint_left.mp parts.2.2.2.2 h present
  simp [keyRank,different,keyRank_absent absent]

theorem double_amortized {key : α} {before after : RawTree α}
    (step : Double key before after) (unique : (inorder before).Nodup) :
    2 + 2*potential after + 6*keyRank key before ≤
      2*potential before + 6*keyRank key after := by
  induction step with
  | leftLeft a b c d y z =>
      rw [keyRank_left unique (by simp [inorder]),
        keyRank_left (nodup_node unique).1 (by simp [inorder]),keyRank_root,keyRank_root]
      have disjoint := disjoint_ranks
        (a := size a+1+size b) (b := size c+1+size d)
        (total := size a+1+(size b+1+(size c+1+size d))) (by omega) (by omega) (by omega)
      have lower : rank (.node a key b) ≤ rank (.node (.node a key b) y c) :=
        rank_mono (by simp only [size]; omega)
      have upper : rank (.node b y (.node c z d)) ≤ rank (.node a key (.node b y (.node c z d))) :=
        rank_mono (by simp only [size]; omega)
      simp only [potential,rank,size] at *
      have same : size a+1+size b+1+size c+1+size d = size a+1+(size b+1+(size c+1+size d)) := by omega
      rw [same]
      omega
  | rightRight a b c d x y =>
      rw [keyRank_right unique (by simp [inorder]),
        keyRank_right (nodup_node unique).2.1 (by simp [inorder]),keyRank_root,keyRank_root]
      have disjoint := disjoint_ranks
        (a := size a+1+size b) (b := size c+1+size d)
        (total := ((size a+1+size b)+1+size c)+1+size d) (by omega) (by omega) (by omega)
      have lower : rank (.node c key d) ≤ rank (.node b y (.node c key d)) :=
        rank_mono (by simp only [size]; omega)
      have upper : rank (.node (.node a x b) y c) ≤ rank (.node (.node (.node a x b) y c) key d) :=
        rank_mono (by simp only [size]; omega)
      simp only [potential,rank,size] at *
      have same : size a+1+(size b+1+(size c+1+size d)) = size a+1+size b+1+size c+1+size d := by omega
      rw [same]
      omega
  | leftRight a b c d x z =>
      rw [keyRank_left unique (by simp [inorder]),
        keyRank_right (nodup_node unique).1 (by simp [inorder]),keyRank_root,keyRank_root]
      have disjoint := disjoint_ranks
        (a := size a+1+size b) (b := size c+1+size d)
        (total := (size a+1+size b)+1+(size c+1+size d)) (by omega) (by omega) (by omega)
      have lower : rank (.node b key c) ≤ rank (.node a x (.node b key c)) :=
        rank_mono (by simp only [size]; omega)
      have root : rank (.node b key c) ≤ rank (.node (.node a x b) key (.node c z d)) :=
        rank_mono (by simp only [size]; omega)
      simp only [potential,rank,size] at *
      have same : size a+1+(size b+1+size c)+1+size d = (size a+1+size b)+1+(size c+1+size d) := by omega
      rw [same]
      omega
  | rightLeft a b c d x z =>
      rw [keyRank_right unique (by simp [inorder]),
        keyRank_left (nodup_node unique).2.1 (by simp [inorder]),keyRank_root,keyRank_root]
      have disjoint := disjoint_ranks
        (a := size a+1+size b) (b := size c+1+size d)
        (total := (size a+1+size b)+1+(size c+1+size d)) (by omega) (by omega) (by omega)
      have lower : rank (.node b key c) ≤ rank (.node (.node b key c) z d) :=
        rank_mono (by simp only [size]; omega)
      have root : rank (.node b key c) ≤ rank (.node (.node a x b) key (.node c z d)) :=
        rank_mono (by simp only [size]; omega)
      simp only [potential,rank,size] at *
      have same : size a+1+(size b+1+size c+1+size d) = (size a+1+size b)+1+(size c+1+size d) := by omega
      rw [same]
      omega
  | @leftContext a b step pivot right ih =>
      have parts := nodup_node unique
      have wholeAfter : (inorder (.node b pivot right)).Nodup := by
        simpa only [inorder,← step.inorder_eq] using unique
      rw [keyRank_left unique step.member,
        keyRank_left wholeAfter (step.inorder_eq ▸ step.member)]
      have same : size a = size b := by
        rw [← ChaCha.MTR.Tree.length_inorder,← ChaCha.MTR.Tree.length_inorder,step.inorder_eq]
      have localBound := ih parts.1
      simp only [potential,rank,size,same]
      omega
  | @rightContext left pivot a b step ih =>
      have parts := nodup_node unique
      have wholeAfter : (inorder (.node left pivot b)).Nodup := by
        simpa only [inorder,← step.inorder_eq] using unique
      rw [keyRank_right unique step.member,
        keyRank_right wholeAfter (step.inorder_eq ▸ step.member)]
      have same : size a = size b := by
        rw [← ChaCha.MTR.Tree.length_inorder,← ChaCha.MTR.Tree.length_inorder,step.inorder_eq]
      have localBound := ih parts.2.1
      simp only [potential,rank,size,same]
      omega

/-- The integer access lemma, including the single possible final zig. -/
theorem splay_amortized_rank {key : α} {before after : RawTree α} {rotations : Nat}
    (execution : Splay key before after rotations) (unique : (inorder before).Nodup) :
    rotations + 2*potential after + 6*keyRank key before ≤
      2*potential before + 6*keyRank key after + 1 := by
  induction execution with
  | done left right => omega
  | @next before middle after head tail step rest ih =>
      have uniqueMiddle : (inorder middle).Nodup := step.inorder_eq ▸ unique
      cases step with
      | zigLeft a b c y =>
          obtain ⟨rfl,rfl⟩ := rest.deterministic (.done a (.node b y c)) uniqueMiddle
          rw [keyRank_left unique (by simp [inorder]),keyRank_root,keyRank_root]
          have old : rank (.node a key b) ≤ rank (.node a key (.node b y c)) :=
            rank_mono (by simp only [size]; omega)
          have fresh : rank (.node b y c) ≤ rank (.node a key (.node b y c)) :=
            rank_mono (by simp only [size]; omega)
          simp only [potential,rank,size] at *
          have same : size a+1+size b+1+size c = size a+1+(size b+1+size c) := by omega
          rw [same]
          omega
      | zigRight a b c x =>
          obtain ⟨rfl,rfl⟩ := rest.deterministic (.done (.node a x b) c) uniqueMiddle
          rw [keyRank_right unique (by simp [inorder]),keyRank_root,keyRank_root]
          have old : rank (.node b key c) ≤ rank (.node (.node a x b) key c) :=
            rank_mono (by simp only [size]; omega)
          have fresh : rank (.node a x b) ≤ rank (.node (.node a x b) key c) :=
            rank_mono (by simp only [size]; omega)
          simp only [potential,rank,size] at *
          have same : size a+1+(size b+1+size c) = size a+1+size b+1+size c := by omega
          rw [same]
          omega
      | double doubled =>
          have first := double_amortized doubled unique
          have remaining := ih uniqueMiddle
          omega

/-- Unweighted logarithmic amortization for the actual splay transcript. -/
theorem splay_amortized {key : α} {before after : RawTree α} {rotations : Nat}
    (execution : Splay key before after rotations) (unique : (inorder before).Nodup) :
    rotations + 2*potential after ≤ 2*potential before + 6*rank before + 1 := by
  have bound := splay_amortized_rank execution unique
  have root := execution.root_after
  have endpoint : keyRank key after = rank after := by
    cases after with
    | empty => simp [rootKey] at root
    | node left pivot right =>
        have same : pivot = key := Option.some.inj root
        subst pivot
        exact keyRank_root _ _ _
  rw [endpoint] at bound
  have same : rank after = rank before := congrArg (Nat.log 2) execution.size_eq.symm
  rw [same] at bound
  omega

theorem splay_amortized_capacity {key : α} {before after : RawTree α} {rotations capacity : Nat}
    (execution : Splay key before after rotations) (unique : (inorder before).Nodup)
    (bounded : size before ≤ capacity) :
    rotations + 2*potential after ≤ 2*potential before + 6*Nat.log 2 capacity + 1 := by
  have bound := splay_amortized execution unique
  have cap : rank before ≤ Nat.log 2 capacity := Nat.log_mono_right bounded
  omega

end KeyRank

end ChaCha.Paper20261030.SplayAuxiliary
