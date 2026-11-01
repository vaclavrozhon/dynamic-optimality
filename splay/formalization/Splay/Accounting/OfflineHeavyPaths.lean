import Splay.Accounting.OfflineContextExposure
import Splay.Analysis.PolylogHeightFactor

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree FrontierFolding

namespace FrontierFolding.Context

def AllSideTrees (property : {lower upper : ℕ} → BST lower upper → Prop)
    {lower innerLower innerUpper upper : ℕ} : Context lower innerLower innerUpper upper → Prop
  | .hole _ _ => True
  | .low left tail => property left ∧ tail.AllSideTrees property
  | .high initial right => initial.AllSideTrees property ∧ property right

theorem AllSideTrees.imp {property other : {lower upper : ℕ} → BST lower upper → Prop}
    {lower innerLower innerUpper upper : ℕ} {context : Context lower innerLower innerUpper upper}
    (trees : context.AllSideTrees property)
    (implies : ∀ {lo hi : ℕ} (tree : BST lo hi), property tree → other tree) :
    context.AllSideTrees other := by
  induction context with
  | hole => trivial
  | low left tail ih => exact ⟨implies left trees.1, ih trees.2⟩
  | high initial right ih => exact ⟨ih trees.1, implies right trees.2⟩

/-- The selected child is larger, with a left preference on ties. -/
def IsLong {lower innerLower innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : BST innerLower innerUpper) : Prop :=
  match context with
  | .hole _ _ => True
  | .low left tail => left.size < (tail.plug core).size ∧ tail.IsLong core
  | .high initial right => right.size ≤ (initial.plug core).size ∧ initial.IsLong core

theorem word_length_add_core_size_le {lower innerLower innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : BST innerLower innerUpper) :
    context.word.length + core.size ≤ (context.plug core).size := by
  induction context with
  | hole => simp [Context.word, Context.plug]
  | low left tail ih =>
      have rest := ih core
      simp only [Context.word, List.length_cons, Context.plug, BST.size]
      omega
  | high initial right ih =>
      have rest := ih core
      simp only [Context.word, List.length_cons, Context.plug, BST.size]
      omega

theorem IsLong.side_half {lower innerLower innerUpper upper : ℕ}
    {context : Context lower innerLower innerUpper upper} {core : BST innerLower innerUpper}
    (long : context.IsLong core) :
    context.AllSideTrees (fun payload => 2 * (payload.size + 1) ≤ (context.plug core).size + 1) := by
  induction context with
  | hole => trivial
  | low left tail ih =>
      have rest := ih long.2
      refine ⟨?_, rest.imp (fun payload bound => ?_)⟩
      · have heavier := long.1
        simp only [Context.plug, BST.size]
        omega
      · simp only [Context.plug, BST.size]
        omega
  | high initial right ih =>
      have rest := ih long.2
      refine ⟨rest.imp (fun payload bound => ?_), ?_⟩
      · simp only [Context.plug, BST.size]
        omega
      · have heavier := long.1
        simp only [Context.plug, BST.size]
        omega

theorem expose_allPayloads {property : {lo hi : ℕ} → BST lo hi → Prop}
    {lower innerLower root innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : RootSplit innerLower root innerUpper)
    (sides : context.AllSideTrees property)
    (leaves : core.leftSelected.frontier.AllPayloads property ∧ core.rightSelected.frontier.AllPayloads property) :
    (context.expose core).leftSelected.frontier.AllPayloads property ∧
      (context.expose core).rightSelected.frontier.AllPayloads property := by
  induction context with
  | hole => exact leaves
  | low left tail ih =>
      obtain ⟨leftPayloads, rightPayloads⟩ := ih core sides.2 leaves
      exact ⟨⟨sides.1, leftPayloads⟩, rightPayloads⟩
  | high initial right ih =>
      obtain ⟨leftPayloads, rightPayloads⟩ := ih core sides.1 leaves
      refine ⟨leftPayloads, ?_⟩
      exact (SupportFrontier.allPayloads_append _ _).mpr ⟨rightPayloads, sides.2⟩

theorem expose_card {lower innerLower root innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : RootSplit innerLower root innerUpper) :
    (context.expose core).leftSelected.card + (context.expose core).rightSelected.card =
      context.word.length + core.leftSelected.card + core.rightSelected.card := by
  have same := (context.exposurePath core).toExecution.card_eq
  rw [card_liftSelected] at same
  simp only [RootPrefix.card] at same
  omega

end FrontierFolding.Context

/-- Follow the larger child (left on ties) to a leaf. Every hanging subtree
is at most half the current total, including its external-leaf unit. -/
theorem exists_heavyContext {lower upper : ℕ} (tree : BST lower upper) (positive : 0 < tree.size) :
    ∃ (root : ℕ) (context : Context lower root (root + 1) upper),
      tree = context.plug (.node (.empty root) (.empty (root + 1))) ∧
      context.IsLong (.node (.empty root) (.empty (root + 1))) ∧
      context.AllSideTrees (fun payload => 2 * (payload.size + 1) ≤ tree.size + 1) ∧
      context.word.length + 1 ≤ tree.size := by
  induction tree with
  | empty => simp [BST.size] at positive
  | @node lower root upper left right ihL ihR =>
      by_cases leftEmpty : left.size = 0
      · by_cases rightEmpty : right.size = 0
        · cases left with
          | empty =>
              cases right with
              | empty => exact ⟨_, .hole _ _, rfl, trivial, trivial, le_rfl⟩
              | node => simp [BST.size] at rightEmpty
          | node => simp [BST.size] at leftEmpty
        · obtain ⟨key, context, same, long, sideTrees, length⟩ := ihR (by omega)
          have sides := sideTrees.imp (fun payload bound => show
            2 * (payload.size + 1) ≤ (BST.node left right).size + 1 from by
              simp only [BST.size]
              omega)
          refine ⟨key, .low left context, by simp [Context.plug, ← same], ?_, ⟨?_, sides⟩, ?_⟩
          · exact ⟨by simpa only [← same] using (show left.size < right.size by omega), long⟩
          · simp [BST.size, leftEmpty]
          · simp only [Context.word, List.length_cons, BST.size]
            omega
      · by_cases leftHeavier : right.size ≤ left.size
        · obtain ⟨key, context, same, long, sideTrees, length⟩ := ihL (by omega)
          have sides := sideTrees.imp (fun payload bound => show
            2 * (payload.size + 1) ≤ (BST.node left right).size + 1 from by
              simp only [BST.size]
              omega)
          refine ⟨key, .high context right, by simp [Context.plug, ← same], ?_, ⟨sides, ?_⟩, ?_⟩
          · exact ⟨by simpa only [← same] using leftHeavier, long⟩
          · simp only [BST.size]
            omega
          · simp only [Context.word, List.length_cons, BST.size]
            omega
        · obtain ⟨key, context, same, long, sideTrees, length⟩ := ihR (by omega)
          have sides := sideTrees.imp (fun payload bound => show
            2 * (payload.size + 1) ≤ (BST.node left right).size + 1 from by
              simp only [BST.size]
              omega)
          refine ⟨key, .low left context, by simp [Context.plug, ← same], ?_, ⟨?_, sides⟩, ?_⟩
          · exact ⟨by simpa only [← same] using (show left.size < right.size by omega), long⟩
          · simp only [BST.size]
            omega
          · simp only [Context.word, List.length_cons, BST.size]
            omega

/-- Crossing a light edge decreases the upper logarithm by at least one. -/
theorem clog_succ_child_lt {parent child : ℕ} (half : 2 * (child + 1) ≤ parent + 1) :
    Nat.clog 2 (child + 1) + 1 ≤ Nat.clog 2 (parent + 1) := by
  have parentPower : parent + 1 ≤ 2 ^ Nat.clog 2 (parent + 1) := Nat.le_pow_clog (by decide) _
  generalize logarithm : Nat.clog 2 (parent + 1) = level at *
  cases level with
  | zero => simp only [pow_zero] at parentPower; omega
  | succ level =>
      have childPower : child + 1 ≤ 2 ^ level := by
        simp only [pow_succ] at parentPower
        omega
      have childLog := Nat.clog_le_of_le_pow childPower
      omega

/-- An unweighted logarithmic-height stack at each long path gives a
quadratic-logarithmic height bound; leaf weights are unnecessary here. -/
theorem heavyPath_height_step {parent child payloadHeight templateHeight : ℕ}
    (half : 2 * (child + 1) ≤ parent + 1)
    (payload : payloadHeight ≤ 6 * (Nat.clog 2 (child + 1)) ^ 2)
    (template : templateHeight ≤ 5 * Nat.clog 2 (parent + 1)) :
    templateHeight + payloadHeight + 1 ≤ 6 * (Nat.clog 2 (parent + 1)) ^ 2 := by
  have logarithms := clog_succ_child_lt half
  have squares := Nat.pow_le_pow_left logarithms 2
  nlinarith

theorem quadratic_height_step {level : ℕ} (positive : 0 < level) :
    5 * level + 6 * (level - 1) ^ 2 + 1 ≤ 6 * level ^ 2 := by
  cases level with
  | zero => omega
  | succ level => simp only [Nat.add_sub_cancel]; nlinarith

end Splay.Accounting.OfflineConnectedSupport
