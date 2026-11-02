import ChaCha.PointerModel

/-!
# Promotion of one internal leased child

The parent exposes the two caps of its leased gap. The child keeps its
minimum and maximum as an outer shell. Three rotations, with seven actual
pointer operations including navigation, promote that child and preserve
all five opaque frontier trees. The reverse trace works for arbitrary
current frontier trees, including a child body changed while promoted.

This is a two-host structural lemma. It does not make all suspended ancestor
headers constant-depth in an unbounded continuation chain.
-/

namespace ChaCha.MTR.InternalLeasePromotion

open Tree Pointer

variable {α : Type*}

/-- Parent caps `a,b`; child caps `c,d`; five literal opaque trees. -/
def nested (a b c d : α) (L U I V R : Tree α) : Tree α :=
  .node L a (.node (.node U c (.node I d V)) b R)

/-- The child shell is outermost, with the parent fragments in its two
exterior gaps. The parent header can remain at `a`. -/
def promoted (a b c d : α) (L U I V R : Tree α) : Tree α :=
  .node (.node L a U) c (.node I d (.node V b R))

theorem same_inorder (a b c d : α) (L U I V R : Tree α) :
    inorder (nested a b c d L U I V R) =
      inorder (promoted a b c d L U I V R) := by
  simp [nested, promoted, inorder, List.append_assoc]

/-- The trace visits only the four caps. It is valid within any actual
ancestor zipper, and never traverses an opaque frontier. -/
theorem promote (a b c d : α) (L U I V R : Tree α)
    (rest : List (Frame α)) :
    Trace ⟨nested a b c d L U I V R, rest⟩ []
      ⟨promoted a b c d L U I V R, rest⟩ 7 := by
  exact .step (.right _ _ _ _ _ _)
    (.step (.rotateRight _ _ _ _ _ _)
      (.step (.upRight _ _ _ _)
        (.step (.rotateLeft _ _ _ _ _ _)
          (.step (.right _ _ _ _ _ _)
            (.step (.rotateRight _ _ _ _ _ _)
              (.step (.upRight _ _ _ _) (.nil _)))))))

/-- Restoration does not require the old child body: `I`, `U`, and `V`
may be their current values after arbitrary permitted child work. -/
theorem restore (a b c d : α) (L U I V R : Tree α)
    (rest : List (Frame α)) :
    Trace ⟨promoted a b c d L U I V R, rest⟩ []
      ⟨nested a b c d L U I V R, rest⟩ 7 := by
  exact .step (.right _ _ _ _ _ _)
    (.step (.rotateLeft _ _ _ _ _ _)
      (.step (.upRight _ _ _ _)
        (.step (.rotateRight _ _ _ _ _ _)
          (.step (.right _ _ _ _ _ _)
            (.step (.rotateLeft _ _ _ _ _ _)
              (.step (.upRight _ _ _ _) (.nil _)))))))

/-- The sole parent header at `a` is reached by one real left move. -/
theorem parent_header (a b c d : α) (L U I V R : Tree α)
    (rest : List (Frame α)) :
    Step ⟨promoted a b c d L U I V R, rest⟩
      ⟨.node L a U, .left c (.node I d (.node V b R)) :: rest⟩ :=
  .left _ _ _ _ _ _

/-- A singleton child has the same interface with two rotations and four
pointer operations. -/
theorem promote_singleton (a b c : α) (L U V R : Tree α)
    (rest : List (Frame α)) :
    Trace ⟨.node L a (.node (.node U c V) b R), rest⟩ []
      ⟨.node (.node L a U) c (.node V b R), rest⟩ 4 := by
  exact .step (.right _ _ _ _ _ _)
    (.step (.rotateRight _ _ _ _ _ _)
      (.step (.upRight _ _ _ _)
        (.step (.rotateLeft _ _ _ _ _ _) (.nil _))))

theorem restore_singleton (a b c : α) (L U V R : Tree α)
    (rest : List (Frame α)) :
    Trace ⟨.node (.node L a U) c (.node V b R), rest⟩ []
      ⟨.node L a (.node (.node U c V) b R), rest⟩ 4 := by
  exact .step (.rotateRight _ _ _ _ _ _)
    (.step (.right _ _ _ _ _ _)
      (.step (.rotateLeft _ _ _ _ _ _)
        (.step (.upRight _ _ _ _) (.nil _))))

end ChaCha.MTR.InternalLeasePromotion
