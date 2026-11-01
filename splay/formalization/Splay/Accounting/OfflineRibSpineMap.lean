import Splay.Accounting.RibStackFoldedFilledGeometry

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm OfflineNormalForm.RibStack

/-- Replace the left payloads of a right spine while retaining its actual keys. -/
inductive RightSpineMap (Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type) :
    {lower upper : ℕ} → BST lower upper → SupportFrontier lower upper → Type
  | empty (boundary : ℕ) : RightSpineMap @Relation (.empty boundary) (.last (.empty boundary))
  | node {lower root upper : ℕ} {left actualLeft : BST lower root} {right : BST (root + 1) upper}
      {tail : SupportFrontier (root + 1) upper}
      (payload : Relation left actualLeft) (rest : RightSpineMap @Relation right tail) :
      RightSpineMap @Relation (.node left right) (.next actualLeft tail)

/-- The symmetric map of a left spine and its right payloads. -/
inductive LeftSpineMap (Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type) :
    {lower upper : ℕ} → BST lower upper → SupportFrontier lower upper → Type
  | empty (boundary : ℕ) : LeftSpineMap @Relation (.empty boundary) (.last (.empty boundary))
  | node {lower root upper : ℕ} {left : BST lower root} {right actualRight : BST (root + 1) upper}
      {initial : SupportFrontier lower root}
      (rest : LeftSpineMap @Relation left initial) (payload : Relation right actualRight) :
      LeftSpineMap @Relation (.node left right) (initial.append (.last actualRight))

namespace RightSpineMap

theorem card_le_size {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper : ℕ} {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : RightSpineMap @Relation before frontier) : frontier.card ≤ before.size := by
  induction mapped with
  | empty => rfl
  | node payload rest ih => simp only [SupportFrontier.card, BST.size]; omega

theorem lastRightBoundary {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper : ℕ} {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : RightSpineMap @Relation before frontier) : frontier.lastRightBoundary = 0 := by
  induction mapped with
  | empty => rfl
  | node payload rest ih => exact ih

/-- Every payload is a strictly smaller source subtree. The separate size
and height limits support both well-founded recursion and geometric estimates. -/
theorem transfer {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {property : {lo hi : ℕ} → BST lo hi → Prop} {lower upper limit height : ℕ}
    {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : RightSpineMap @Relation before frontier) (size : before.size ≤ limit) (depth : before.height ≤ height)
    (empty : ∀ boundary, property (.empty boundary))
    (convert : ∀ {lo hi : ℕ} {source target : BST lo hi}, Relation source target →
      source.size < limit → source.height < height → property target) :
    frontier.AllPayloads property := by
  induction mapped with
  | empty => exact empty _
  | node payload rest ih =>
      simp only [BST.size, BST.height] at size depth
      exact ⟨convert payload (by omega) (by omega), ih (by omega) (by omega)⟩

end RightSpineMap

namespace LeftSpineMap

theorem card_le_size {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper : ℕ} {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : LeftSpineMap @Relation before frontier) : frontier.card ≤ before.size := by
  induction mapped with
  | empty => rfl
  | node rest payload ih => simp only [SupportFrontier.card_append, SupportFrontier.card, BST.size]; omega

theorem firstLeftBoundary {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper : ℕ} {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : LeftSpineMap @Relation before frontier) : frontier.firstLeftBoundary = 0 := by
  induction mapped with
  | empty => rfl
  | node rest payload ih => simpa only [SupportFrontier.firstLeftBoundary_append] using ih

theorem transfer {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {property : {lo hi : ℕ} → BST lo hi → Prop} {lower upper limit height : ℕ}
    {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : LeftSpineMap @Relation before frontier) (size : before.size ≤ limit) (depth : before.height ≤ height)
    (empty : ∀ boundary, property (.empty boundary))
    (convert : ∀ {lo hi : ℕ} {source target : BST lo hi}, Relation source target →
      source.size < limit → source.height < height → property target) :
    frontier.AllPayloads property := by
  induction mapped with
  | empty => exact empty _
  | node rest payload ih =>
      simp only [BST.size, BST.height] at size depth
      exact (SupportFrontier.allPayloads_append _ _).mpr
        ⟨ih (by omega) (by omega), convert payload (by omega) (by omega)⟩

end LeftSpineMap

theorem RightSpineMap.exists_map {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper limit : ℕ} (before : BST lower upper) (fits : before.size ≤ limit)
    (realize : ∀ {lo hi : ℕ} (source : BST lo hi), source.size < limit →
      ∃ target : BST lo hi, Nonempty (Relation source target)) :
    ∃ frontier : SupportFrontier lower upper, Nonempty (RightSpineMap @Relation before frontier) := by
  induction before with
  | empty => exact ⟨_, ⟨.empty _⟩⟩
  | node left right ihL ihR =>
      simp only [BST.size] at fits
      obtain ⟨actualLeft, ⟨payload⟩⟩ := realize left (by omega)
      obtain ⟨tail, ⟨mapped⟩⟩ := ihR (by omega)
      exact ⟨.next actualLeft tail, ⟨.node payload mapped⟩⟩

theorem LeftSpineMap.exists_map {Relation : {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper limit : ℕ} (before : BST lower upper) (fits : before.size ≤ limit)
    (realize : ∀ {lo hi : ℕ} (source : BST lo hi), source.size < limit →
      ∃ target : BST lo hi, Nonempty (Relation source target)) :
    ∃ frontier : SupportFrontier lower upper, Nonempty (LeftSpineMap @Relation before frontier) := by
  induction before with
  | empty => exact ⟨_, ⟨.empty _⟩⟩
  | node left right ihL ihR =>
      simp only [BST.size] at fits
      obtain ⟨initial, ⟨mapped⟩⟩ := ihL (by omega)
      obtain ⟨actualRight, ⟨payload⟩⟩ := realize right (by omega)
      exact ⟨initial.append (.last actualRight), ⟨.node mapped payload⟩⟩

theorem SupportFrontier.AllPayloads.imp {property other : {lo hi : ℕ} → BST lo hi → Prop}
    {lower upper : ℕ} {frontier : SupportFrontier lower upper} (payloads : frontier.AllPayloads property)
    (convert : ∀ {lo hi : ℕ} (tree : BST lo hi), property tree → other tree) : frontier.AllPayloads other := by
  induction frontier with
  | last tree => exact convert tree payloads
  | next tree tail ih => exact ⟨convert tree payloads.1, ih payloads.2⟩

theorem SupportFrontier.firstLeftBoundary_le {lower upper bound : ℕ} {frontier : SupportFrontier lower upper}
    (payloads : frontier.AllPayloads (fun tree => leftBoundaryDepth tree ≤ bound)) : frontier.firstLeftBoundary ≤ bound := by
  cases frontier with
  | last => exact payloads
  | next => exact payloads.1

theorem SupportFrontier.lastRightBoundary_le {lower upper bound : ℕ} {frontier : SupportFrontier lower upper}
    (payloads : frontier.AllPayloads (fun tree => rightBoundaryDepth tree ≤ bound)) : frontier.lastRightBoundary ≤ bound := by
  induction frontier with
  | last => exact payloads
  | next tree tail ih => exact ih payloads.2

end Splay.Accounting.OfflineConnectedSupport
