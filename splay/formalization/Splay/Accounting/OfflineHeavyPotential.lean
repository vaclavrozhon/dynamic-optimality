import Splay.Accounting.OfflineHeavyRepresentation

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree FrontierFolding OfflineNormalForm.RibStack

mutual

def HeavyRepresentation.potential {capacity lower upper : ℕ} {before after : BST lower upper}
    (representation : HeavyRepresentation capacity before after) : ℕ :=
  match representation with
  | .empty _ => 0
  | .path payloads _ left right =>
      left.potential + right.potential + payloads.heavyPotential

def FrontierFolding.Context.PayloadMap.heavyPotential
    {capacity lower innerLower innerUpper upper : ℕ}
    {original replacement : Context lower innerLower innerUpper upper}
    (mapped : Context.PayloadMap (@HeavyRepresentation capacity) original replacement) : ℕ :=
  match mapped with
  | .hole _ _ => 0
  | .low payload tail => payload.potential + tail.heavyPotential
  | .high initial payload => initial.heavyPotential + payload.potential

end

/-- Sum local bounds only over the literal side representations of a path. -/
theorem FrontierFolding.Context.PayloadMap.heavyPotential_le_of
    {capacity lower innerLower innerUpper upper limit : ℕ}
    {original replacement : Context lower innerLower innerUpper upper}
    (mapped : Context.PayloadMap (@HeavyRepresentation capacity) original replacement)
    (small : original.AllSideTrees (fun tree => tree.size < limit))
    (bound : ∀ {lo hi : ℕ} {before after : BST lo hi},
      (representation : HeavyRepresentation capacity before after) → before.size < limit →
      representation.potential ≤ 64 * before.size)
    (core : BST innerLower innerUpper) :
    mapped.heavyPotential + 64 * (original.word.length + core.size) ≤
      64 * (original.plug core).size := by
  induction mapped with
  | hole => simp [Context.PayloadMap.heavyPotential, Context.word, Context.plug]
  | low payload tail ih =>
      have side := bound payload small.1
      have rest := ih small.2 core
      simp only [Context.PayloadMap.heavyPotential, Context.word, Context.plug, BST.size, List.length_cons]
      omega
  | high initial payload ih =>
      have rest := ih small.1 core
      have side := bound payload small.2
      simp only [Context.PayloadMap.heavyPotential, Context.word, Context.plug, BST.size, List.length_cons]
      omega

/-- The initial global credit is linear in the number of real keys. -/
theorem HeavyRepresentation.potential_le_size {capacity lower upper : ℕ}
    {before after : BST lower upper} (representation : HeavyRepresentation capacity before after) :
    representation.potential ≤ 64 * before.size := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper with
  | h count ih =>
      cases representation with
      | empty => simp [HeavyRepresentation.potential]
      | path mapped long left right =>
          rename_i root original replacement
          have small := long.side_half.imp (fun child bound => show child.size < count by omega)
          have payloads := mapped.heavyPotential_le_of small
            (fun child smaller => ih _ smaller child rfl) (leafSplit root).tree
          have leftBound := left.potential_le_card
          have rightBound := right.potential_le_card
          have counts := replacement.expose_card (leafSplit root)
          rw [RootPrefix.frontier_card] at leftBound rightBound
          rw [mapped.word_eq] at counts
          simp only [RootPrefix.card] at counts
          simp only [HeavyRepresentation.potential, BST.size] at *
          omega

end Splay.Accounting.OfflineConnectedSupport
