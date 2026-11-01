import Splay.Accounting.OfflineHeavyPaths
import Splay.Accounting.RibStackFilledMaximum

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree FrontierFolding OfflineNormalForm.RibStack

namespace FrontierFolding.Context

/-- Replace side trees along a path, retaining every path key and turn. -/
inductive PayloadMap (Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type) :
    {lower innerLower innerUpper upper : ℕ} →
      Context lower innerLower innerUpper upper → Context lower innerLower innerUpper upper → Type
  | hole (lower upper : ℕ) : PayloadMap @Relation (.hole lower upper) (.hole lower upper)
  | low {lower root innerLower innerUpper upper : ℕ}
      {before after : BST lower root}
      {original replacement : Context (root + 1) innerLower innerUpper upper}
      (payload : Relation before after) (tail : PayloadMap @Relation original replacement) :
      PayloadMap @Relation (.low before original) (.low after replacement)
  | high {lower innerLower innerUpper root upper : ℕ}
      {original replacement : Context lower innerLower innerUpper root}
      {before after : BST (root + 1) upper}
      (initial : PayloadMap @Relation original replacement) (payload : Relation before after) :
      PayloadMap @Relation (.high original before) (.high replacement after)

namespace PayloadMap

theorem word_eq {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower innerLower innerUpper upper : ℕ}
    {original replacement : Context lower innerLower innerUpper upper}
    (mapped : PayloadMap @Relation original replacement) : replacement.word = original.word := by
  induction mapped with
  | hole => rfl
  | low payload tail ih => simp [Context.word, ih]
  | high initial payload ih => simp [Context.word, ih]

theorem transfer {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {property other : {lo hi : ℕ} → BST lo hi → Prop}
    {lower innerLower innerUpper upper : ℕ}
    {original replacement : Context lower innerLower innerUpper upper}
    (mapped : PayloadMap @Relation original replacement) (source : original.AllSideTrees property)
    (convert : ∀ {lo hi : ℕ} {before after : BST lo hi}, Relation before after → property before → other after) :
    replacement.AllSideTrees other := by
  induction mapped with
  | hole => trivial
  | low payload tail ih => exact ⟨convert payload source.1, ih source.2⟩
  | high initial payload ih => exact ⟨ih source.1, convert payload source.2⟩

theorem exists_map {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {property : {lo hi : ℕ} → BST lo hi → Prop}
    {lower innerLower innerUpper upper : ℕ} (original : Context lower innerLower innerUpper upper)
    (source : original.AllSideTrees property)
    (realize : ∀ {lo hi : ℕ} (before : BST lo hi), property before →
      ∃ after : BST lo hi, Nonempty (Relation before after)) :
    ∃ replacement : Context lower innerLower innerUpper upper, Nonempty (PayloadMap @Relation original replacement) := by
  induction original with
  | hole lower upper => exact ⟨.hole lower upper, ⟨.hole lower upper⟩⟩
  | low left tail ih =>
      obtain ⟨after, ⟨payload⟩⟩ := realize left source.1
      obtain ⟨replacement, ⟨mapped⟩⟩ := ih source.2
      exact ⟨.low after replacement, ⟨.low payload mapped⟩⟩
  | high initial right ih =>
      obtain ⟨replacement, ⟨mapped⟩⟩ := ih source.1
      obtain ⟨after, ⟨payload⟩⟩ := realize right source.2
      exact ⟨.high replacement after, ⟨.high mapped payload⟩⟩

end PayloadMap

end FrontierFolding.Context

abbrev leafSplit (root : ℕ) : RootSplit root root (root + 1) :=
  ⟨.empty root, .empty (root + 1), .none _, .none _⟩

/-- A history-dependent two-stack representation of each long path. The
original path and all recursive payload correspondences are retained. -/
inductive HeavyRepresentation (capacity : ℕ) : {lower upper : ℕ} → BST lower upper → BST lower upper → Type
  | empty (boundary : ℕ) : HeavyRepresentation capacity (.empty boundary) (.empty boundary)
  | path {lower root upper : ℕ}
      {original replacement : Context lower root (root + 1) upper}
      (payloads : Context.PayloadMap (@HeavyRepresentation capacity) original replacement)
      (long : original.IsLong (leafSplit root).tree)
      (left : MinimumStack capacity (replacement.expose (leafSplit root)).leftSelected.frontier)
      (right : MaximumStack capacity (replacement.expose (leafSplit root)).rightSelected.frontier) :
      HeavyRepresentation capacity (original.plug (leafSplit root).tree) (.node left.tree right.tree)

namespace HeavyRepresentation

/-- Construct the complete representation, recursively filling both real
stacks with representations of the hanging subtrees. -/
theorem exists_representation {lower upper : ℕ} (capacity : ℕ) (before : BST lower upper)
    (fits : before.size ≤ capacity) :
    ∃ after : BST lower upper, Nonempty (HeavyRepresentation capacity before after) := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper with
  | h count ih =>
      cases before with
      | empty => exact ⟨.empty _, ⟨.empty _⟩⟩
      | node leftTree rightTree =>
          obtain ⟨key, context, same, long, sideTrees, length⟩ :=
            exists_heavyContext (.node leftTree rightTree) (by simp [BST.size])
          obtain ⟨replacement, ⟨mapped⟩⟩ :=
            Context.PayloadMap.exists_map (Relation := @HeavyRepresentation capacity) context sideTrees
              (fun payload bound => ih payload.size (by omega) payload (by omega) rfl)
          have cards := replacement.expose_card (leafSplit key)
          have word := mapped.word_eq
          simp only [RootPrefix.card] at cards
          rw [word] at cards
          have leftFits : (replacement.expose (leafSplit key)).leftSelected.frontier.card ≤ capacity := by
            rw [RootPrefix.frontier_card]
            omega
          have rightFits : (replacement.expose (leafSplit key)).rightSelected.frontier.card ≤ capacity := by
            rw [RootPrefix.frontier_card]
            omega
          obtain ⟨left⟩ := MinimumStack.exists_initial capacity _ leftFits
          obtain ⟨right⟩ := MaximumStack.exists_initial capacity _ rightFits
          refine ⟨.node left.tree right.tree, ?_⟩
          rw [same]
          exact ⟨.path mapped long left right⟩

/-- Every valid history of the unweighted long-path representation has
quadratic-logarithmic height. The bound does not depend on leaf weights. -/
theorem height_le {capacity lower upper : ℕ} {before after : BST lower upper}
    (representation : HeavyRepresentation capacity before after) :
    after.height ≤ 6 * (Nat.clog 2 (before.size + 1)) ^ 2 := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper with
  | h count ih =>
      cases representation with
      | empty boundary => simp [BST.height]
      | path mapped long left right =>
          rename_i root original replacement
          let level := Nat.clog 2 ((original.plug (leafSplit root).tree).size + 1)
          let payloadHeight := 6 * (level - 1) ^ 2
          have half := long.side_half
          have pathBound : original.word.length + 1 ≤ (original.plug (leafSplit root).tree).size := by
            simpa [BST.size] using original.word_length_add_core_size_le (leafSplit root).tree
          have positive : 0 < level := by
            apply Nat.clog_pos (by decide)
            omega
          have payloads : replacement.AllSideTrees (fun payload => payload.height ≤ payloadHeight) := by
            apply mapped.transfer half
            intro lo hi child actual childRepresentation smaller
            have childBound := ih child.size (by omega) childRepresentation rfl
            have childLog := clog_succ_child_lt smaller
            have smallerLog : Nat.clog 2 (child.size + 1) ≤ level - 1 := by
              dsimp [level]
              omega
            exact childBound.trans (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left smallerLog 2))
          have fringePayloads := replacement.expose_allPayloads (leafSplit root) payloads
            (by simp [RootPrefix.frontier, SupportFrontier.AllPayloads, BST.height])
          have leftHeight := left.height_le fringePayloads.1
          have rightHeight := right.height_le fringePayloads.2
          have cards := replacement.expose_card (leafSplit root)
          have word := mapped.word_eq
          simp only [RootPrefix.card] at cards
          rw [word] at cards
          have leftCount : (replacement.expose (leafSplit root)).leftSelected.frontier.card ≤
              (original.plug (leafSplit root).tree).size := by
            rw [RootPrefix.frontier_card]
            omega
          have rightCount : (replacement.expose (leafSplit root)).rightSelected.frontier.card ≤
              (original.plug (leafSplit root).tree).size := by
            rw [RootPrefix.frontier_card]
            omega
          have leftLog := Nat.clog_mono_right 2 (Nat.add_le_add_right leftCount 1)
          have rightLog := Nat.clog_mono_right 2 (Nat.add_le_add_right rightCount 1)
          have step := quadratic_height_step positive
          rw [← sizeEq]
          change max left.tree.height right.tree.height + 1 ≤ 6 * level ^ 2
          dsimp [payloadHeight, level] at *
          omega

end HeavyRepresentation

end Splay.Accounting.OfflineConnectedSupport
