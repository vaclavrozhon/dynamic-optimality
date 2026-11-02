import DynamicOptimality.MultiFinger.HandMovesAdjacency

/-! # Adding a mark adjacent to an already marked source key

The change is either empty or a single anchored endpoint edit. In
particular it can be lifted through arbitrarily many suppressed ancestors
without paying their depth and without cutting an interior tendon.
-/

namespace DynamicOptimality.MultiFinger.Hand

open ChaCha.MTR

variable {α : Type*} [DecidableEq α]

theorem compress_add_root (marked : α → Bool) {left right : RawTree α} {root : α}
    (distinct : (Tree.inorder (.node left root right)).Nodup) :
    compress (addMark marked root) (.node left root right) =
      assemble true (compress marked left) root (compress marked right) := by
  have parts := node_distinct distinct
  rw [compress_assemble, addMark_self,
    compress_add_absent marked left parts.2.2.1,
    compress_add_absent marked right parts.2.2.2.1]

theorem parent_mark_left (marked : Bool) (a b c : Hand α) (child parent : α) :
    AnchoredChange (assemble marked (.node [] a child b) parent c)
      (assemble true (.node [] a child b) parent c) := by
  cases marked with
  | true => exact Or.inl rfl
  | false =>
      cases c with
      | stump tree => exact Or.inr (.inner_left [] a b child parent tree)
      | node frames left key right => exact Or.inl rfl

theorem parent_mark_right (marked : Bool) (a b c : Hand α) (parent child : α) :
    AnchoredChange (assemble marked a parent (.node [] b child c))
      (assemble true a parent (.node [] b child c)) := by
  cases marked with
  | true => exact Or.inl rfl
  | false =>
      cases a with
      | stump tree => exact Or.inr (.inner_right [] b c child parent tree)
      | node frames left key right => exact Or.inl rfl

theorem Adjacent.add_mark {tree : RawTree α} {first last : α}
    (edge : Adjacent tree first last) (distinct : tree.inorder.Nodup)
    (marked : α → Bool) (hit : marked first = true) :
    AnchoredChange (compress marked tree) (compress (addMark marked last) tree) := by
  induction edge with
  | downLeft a b c child parent =>
      have parts := node_distinct distinct
      have member : child ∈ (Tree.inorder (.node a child b)) := by simp [Tree.inorder]
      have different : parent ≠ child := fun equal => parts.2.2.1 (equal ▸ member)
      have absent := parts.2.2.2.2 child member
      have beforeEq : compress marked (.node (.node a child b) parent c) =
          .node [] (compress marked (.node a child b)) parent (compress marked c) := by
        rw [compress_assemble, hit]; rfl
      have afterEq : compress (addMark marked child) (.node (.node a child b) parent c) =
          .node [] (assemble true (compress marked a) child (compress marked b))
            parent (compress marked c) := by
        rw [compress_assemble, addMark_ne marked different, hit,
          compress_add_root marked parts.1, compress_add_absent marked c absent]
        rfl
      rw [beforeEq, afterEq, compress_assemble]
      exact (root_mark (marked child) (compress marked a) child (compress marked b)).left
        [] parent (compress marked c)
  | downRight a b c parent child =>
      have parts := node_distinct distinct
      have member : child ∈ (Tree.inorder (.node b child c)) := by simp [Tree.inorder]
      have different : parent ≠ child := fun equal => parts.2.2.2.1 (equal ▸ member)
      have absent : child ∉ a.inorder := fun leftMember => parts.2.2.2.2 child leftMember member
      have beforeEq : compress marked (.node a parent (.node b child c)) =
          .node [] (compress marked a) parent (compress marked (.node b child c)) := by
        rw [compress_assemble, hit]; rfl
      have afterEq : compress (addMark marked child) (.node a parent (.node b child c)) =
          .node [] (compress marked a) parent
            (assemble true (compress marked b) child (compress marked c)) := by
        rw [compress_assemble, addMark_ne marked different, hit,
          compress_add_absent marked a absent, compress_add_root marked parts.2.1]
        rfl
      rw [beforeEq, afterEq, compress_assemble]
      exact (root_mark (marked child) (compress marked b) child (compress marked c)).right
        [] (compress marked a) parent
  | upLeft a b c child parent =>
      rw [compress_add_root marked distinct, compress_assemble]
      rw [compress_assemble, hit]
      exact parent_mark_left (marked parent) (compress marked a) (compress marked b)
        (compress marked c) child parent
  | upRight a b c parent child =>
      rw [compress_add_root marked distinct, compress_assemble]
      rw [compress_assemble, hit]
      exact parent_mark_right (marked parent) (compress marked a) (compress marked b)
        (compress marked c) parent child
  | @left subtree first last edge root right ih =>
      have parts := node_distinct distinct
      have firstMember := edge.members.1
      have lastMember := edge.members.2
      have different : root ≠ last := fun equal => parts.2.2.1 (equal ▸ lastMember)
      have absent := parts.2.2.2.2 last lastMember
      have change := ih parts.1 hit
      have oldPresent := compress_nonempty marked subtree firstMember hit
      have newHit : addMark marked last first = true := by simp [addMark, hit]
      have newPresent := compress_nonempty (addMark marked last) subtree firstMember newHit
      rw [compress_assemble, compress_assemble, addMark_ne marked different,
        compress_add_absent marked right absent]
      exact change.assemble_left oldPresent newPresent (marked root) root (compress marked right)
  | @right subtree first last edge left root ih =>
      have parts := node_distinct distinct
      have firstMember := edge.members.1
      have lastMember := edge.members.2
      have different : root ≠ last := fun equal => parts.2.2.2.1 (equal ▸ lastMember)
      have absent : last ∉ left.inorder := fun member => parts.2.2.2.2 last member lastMember
      have change := ih parts.2.1 hit
      have oldPresent := compress_nonempty marked subtree firstMember hit
      have newHit : addMark marked last first = true := by simp [addMark, hit]
      have newPresent := compress_nonempty (addMark marked last) subtree firstMember newHit
      rw [compress_assemble, compress_assemble, addMark_ne marked different,
        compress_add_absent marked left absent]
      exact change.assemble_right oldPresent newPresent (marked root) (compress marked left) root

end DynamicOptimality.MultiFinger.Hand
