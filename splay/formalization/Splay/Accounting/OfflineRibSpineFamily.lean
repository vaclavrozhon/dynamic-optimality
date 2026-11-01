import Splay.Accounting.OfflineRibSpineMap

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm

/-- The orientation is an index of this map, while the recursive relation
is passed as one whole family. This keeps nested recursion strictly positive. -/
inductive RibSpineMap (Relation : Bool → {lo hi : ℕ} → BST lo hi → BST lo hi → Type) :
    Bool → {lower upper : ℕ} → BST lower upper → SupportFrontier lower upper → Type
  | empty (side : Bool) (boundary : ℕ) :
      RibSpineMap @Relation side (.empty boundary) (.last (.empty boundary))
  | right {lower root upper : ℕ} {left actualLeft : BST lower root} {right : BST (root + 1) upper}
      {tail : SupportFrontier (root + 1) upper}
      (payload : Relation true left actualLeft) (rest : RibSpineMap @Relation false right tail) :
      RibSpineMap @Relation false (.node left right) (.next actualLeft tail)
  | left {lower root upper : ℕ} {left : BST lower root} {right actualRight : BST (root + 1) upper}
      {initial : SupportFrontier lower root}
      (rest : RibSpineMap @Relation true left initial) (payload : Relation false right actualRight) :
      RibSpineMap @Relation true (.node left right) (initial.append (.last actualRight))

namespace RibSpineMap

theorem card_le_size {Relation : Bool → {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper : ℕ} {side : Bool} {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : RibSpineMap @Relation side before frontier) : frontier.card ≤ before.size := by
  induction mapped with
  | empty => rfl
  | right payload rest ih => simp only [SupportFrontier.card, BST.size]; omega
  | left rest payload ih => simp only [SupportFrontier.card_append, SupportFrontier.card, BST.size]; omega

theorem outer_empty {Relation : Bool → {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper : ℕ} {side : Bool} {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : RibSpineMap @Relation side before frontier) :
    (if side then frontier.firstLeftBoundary else frontier.lastRightBoundary) = 0 := by
  induction mapped with
  | empty side boundary => cases side <;> rfl
  | right payload rest ih => exact ih
  | left rest payload ih => simpa only [if_true, SupportFrontier.firstLeftBoundary_append] using ih

theorem transfer {Relation : Bool → {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {property : {lo hi : ℕ} → BST lo hi → Prop} {lower upper limit height : ℕ} {side : Bool}
    {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : RibSpineMap @Relation side before frontier) (size : before.size ≤ limit) (depth : before.height ≤ height)
    (empty : ∀ boundary, property (.empty boundary))
    (convert : ∀ {lo hi : ℕ} {source target : BST lo hi}, Relation (!side) source target →
      source.size < limit → source.height < height → property target) :
    frontier.AllPayloads property := by
  induction mapped with
  | empty => exact empty _
  | right payload rest ih =>
      simp only [BST.size, BST.height] at size depth
      exact ⟨convert payload (by omega) (by omega), ih (by omega) (by omega) convert⟩
  | left rest payload ih =>
      simp only [BST.size, BST.height] at size depth
      exact (SupportFrontier.allPayloads_append _ _).mpr
        ⟨ih (by omega) (by omega) convert, convert payload (by omega) (by omega)⟩

theorem exists_map {Relation : Bool → {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper limit : ℕ} (side : Bool) (before : BST lower upper) (fits : before.size ≤ limit)
    (realize : ∀ {lo hi : ℕ} (source : BST lo hi), source.size < limit →
      ∃ target : BST lo hi, Nonempty (Relation (!side) source target)) :
    ∃ frontier : SupportFrontier lower upper, Nonempty (RibSpineMap @Relation side before frontier) := by
  induction before generalizing side with
  | empty => exact ⟨_, ⟨.empty side _⟩⟩
  | node left right ihL ihR =>
      simp only [BST.size] at fits
      cases side with
      | false =>
          obtain ⟨actualLeft, ⟨payload⟩⟩ := realize left (by omega)
          obtain ⟨tail, ⟨mapped⟩⟩ := ihR false (by omega) realize
          exact ⟨.next actualLeft tail, ⟨.right payload mapped⟩⟩
      | true =>
          obtain ⟨initial, ⟨mapped⟩⟩ := ihL true (by omega) realize
          obtain ⟨actualRight, ⟨payload⟩⟩ := realize right (by omega)
          exact ⟨initial.append (.last actualRight), ⟨.left mapped payload⟩⟩

end RibSpineMap

end Splay.Accounting.OfflineConnectedSupport
