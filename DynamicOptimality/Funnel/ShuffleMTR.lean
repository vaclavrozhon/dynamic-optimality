import DynamicOptimality.Funnel.VisibilityCharge
import DynamicOptimality.Funnel.Reindex
import DynamicOptimality.Funnel.MTRCost

/-!
# Arbitrary occurrence shuffles and the MTR source bound

A shuffle records increasing occurrence embeddings with disjoint images
covering the output word. These conditions permit repeated keys and
overlapping alphabets, while ruling out dropped or duplicated occurrences.
-/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α]

structure Shuffle (leftWord rightWord output : List α) where
  left : Fin leftWord.length ↪o Fin output.length
  right : Fin rightWord.length ↪o Fin output.length
  left_keys : ∀ p, output.get (left p) = leftWord.get p
  right_keys : ∀ p, output.get (right p) = rightWord.get p
  disjoint : Disjoint (Finset.univ.image left) (Finset.univ.image right)
  cover : Finset.univ.image left ∪ Finset.univ.image right = Finset.univ

omit [LinearOrder α] in
theorem Shuffle.length {X Y W : List α} (shuffle : Shuffle X Y W) :
    W.length = X.length + Y.length := by
  have cards := congrArg Finset.card shuffle.cover
  rw [Finset.card_union_of_disjoint shuffle.disjoint,
    Finset.card_image_of_injective _ shuffle.left.injective,
    Finset.card_image_of_injective _ shuffle.right.injective] at cards
  simpa only [Finset.card_univ,Fintype.card_fin] using cards.symm

theorem Shuffle.visibility_bound {X Y W : List α} (shuffle : Shuffle X Y W) :
    wordCount W ≤ 3*(wordEdgeCount X + wordEdgeCount Y) := by
  classical
  let leftImage := Finset.univ.image shuffle.left
  let rightImage := Finset.univ.image shuffle.right
  let color (p : Fin W.length) : Bool := decide (p ∈ rightImage)
  have rightClass : colorClass Finset.univ color true = rightImage := by
    ext p
    simp [colorClass,color]
  have leftClass : colorClass Finset.univ color false = leftImage := by
    ext p
    simp only [colorClass,Finset.mem_filter,Finset.mem_univ,true_and,color,
      decide_eq_false_iff_not]
    constructor
    · intro outside
      have covered : p ∈ leftImage ∪ rightImage := by rw [shuffle.cover]; exact Finset.mem_univ _
      exact (Finset.mem_union.mp covered).resolve_right outside
    · intro inside
      exact fun both => (Finset.disjoint_left.mp shuffle.disjoint) inside both
  have leftCount : edgeCount W.get leftImage = wordEdgeCount X := by
    rw [edgeCount_reindex]
    have functions : W.get ∘ shuffle.left = X.get := funext shuffle.left_keys
    rw [functions]
    rfl
  have rightCount : edgeCount W.get rightImage = wordEdgeCount Y := by
    rw [edgeCount_reindex]
    have functions : W.get ∘ shuffle.right = Y.get := funext shuffle.right_keys
    rw [functions]
    rfl
  have bound := word_two_color_visibility_charge W color
  rw [leftClass,rightClass,leftCount,rightCount] at bound
  exact bound

/-- A source MTR execution is an actual algorithm execution, not a
numerical oracle. The two sources may start in independently chosen trees. -/
theorem Shuffle.mtr_bound {X Y W : List α} (shuffle : Shuffle X Y W)
    (leftTree rightTree : ChaCha.MTR.Tree α)
    (leftSuccess : ChaCha.MTR.Tree.Successful leftTree X)
    (rightSuccess : ChaCha.MTR.Tree.Successful rightTree Y) :
    wordCount W + W.length ≤ 3 *
      (ChaCha.MTR.runCost leftTree X + ChaCha.MTR.runCost rightTree Y) := by
  have left := edges_add_length_le_mtrCost leftTree X leftSuccess
  have right := edges_add_length_le_mtrCost rightTree Y rightSuccess
  have visibility := shuffle.visibility_bound
  have length := shuffle.length
  omega

end DynamicOptimality.Funnel
