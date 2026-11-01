import Splay.Accounting.JunctionAttachmentOrder

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree

def edgeBetween {n : ℕ} (first middle last : Edge n) : Prop :=
  (edgeStrictlyAbove first middle ∧ edgeStrictlyAbove middle last) ∨
    (edgeStrictlyAbove last middle ∧ edgeStrictlyAbove middle first)

/-- The same unbroken invariant on a subtree's actual edge list. Absolute
attachment depths may be shifted when the subtree acquires new ancestors. -/
def EdgeBlockUnbroken {n : ℕ} (edges : List (Edge n)) (block : Block n) : Prop :=
  ∀ first ∈ edges, first.child ∈ block.elements →
    ∀ last ∈ edges, last.child ∈ block.elements →
      ∀ middle ∈ edges, middle.owner = block.owner → middle.side ≠ block.side →
        ¬ edgeBetween first middle last

theorem edgeBlockUnbroken_iff_canonical {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (block : Block n) :
    EdgeBlockUnbroken (fullEdges snapshot tree) block ↔ canonicalBlockCrossSideUnbroken snapshot tree block := by
  constructor
  · intro unbroken first firstIn last lastIn middle parent opposite between
    have oriented : ∀ first ∈ block.elements, ∀ last ∈ block.elements,
        ChildStrictlyAbove snapshot tree first middle → ChildStrictlyAbove snapshot tree middle last → False := by
      intro first firstIn last lastIn above below
      obtain ⟨firstEdge, middleEdge, firstLookup, middleLookup, above⟩ := above
      obtain ⟨middleEdge', lastEdge, middleLookup', lastLookup, below⟩ := below
      have equal : middleEdge' = middleEdge := Option.some.inj (middleLookup'.symm.trans middleLookup)
      subst middleEdge'
      have firstSpec := incomingEdge?_some_mem snapshot tree firstLookup
      have middleSpec := incomingEdge?_some_mem snapshot tree middleLookup
      have lastSpec := incomingEdge?_some_mem snapshot tree lastLookup
      apply unbroken firstEdge firstSpec.1 (by simpa only [firstSpec.2] using firstIn)
        lastEdge lastSpec.1 (by simpa only [lastSpec.2] using lastIn) middleEdge middleSpec.1
      · simpa only [canonicalParent, middleLookup, Option.map_some, Option.some.injEq] using parent
      · simpa only [canonicalSide, middleLookup] using opposite
      · exact Or.inl ⟨above, below⟩
    rcases between with ⟨above, below⟩ | ⟨above, below⟩
    · exact oriented first firstIn last lastIn above below
    · exact oriented last lastIn first firstIn above below
  · intro unbroken first firstMember firstIn last lastMember lastIn middle middleMember owner opposite between
    have firstLookup := incomingEdge_eq_some_of_mem_fullEdges snapshot tree firstMember
    have lastLookup := incomingEdge_eq_some_of_mem_fullEdges snapshot tree lastMember
    have middleLookup := incomingEdge_eq_some_of_mem_fullEdges snapshot tree middleMember
    apply unbroken first.child firstIn last.child lastIn middle.child
    · simp only [canonicalParent, middleLookup, Option.map_some, owner]
    · simpa only [canonicalSide, middleLookup] using opposite
    · rcases between with ⟨above, below⟩ | ⟨above, below⟩
      · exact Or.inl ⟨⟨first, middle, firstLookup, middleLookup, above⟩, ⟨middle, last, middleLookup, lastLookup, below⟩⟩
      · exact Or.inr ⟨⟨last, middle, lastLookup, middleLookup, above⟩, ⟨middle, first, middleLookup, firstLookup, below⟩⟩

def shiftEdgeDepth {n : ℕ} (amount : ℕ) (edge : Edge n) : Edge n :=
  { edge with attachmentDepth := edge.attachmentDepth + amount }

theorem edgeStrictlyAbove_shift_iff {n : ℕ} (amount : ℕ) (first second : Edge n) :
    edgeStrictlyAbove (shiftEdgeDepth amount first) (shiftEdgeDepth amount second) ↔ edgeStrictlyAbove first second := by
  simp only [edgeStrictlyAbove, shiftEdgeDepth, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]

theorem edgeBetween_shift_iff {n : ℕ} (amount : ℕ) (first middle last : Edge n) :
    edgeBetween (shiftEdgeDepth amount first) (shiftEdgeDepth amount middle) (shiftEdgeDepth amount last) ↔
      edgeBetween first middle last := by
  simp only [edgeBetween, edgeStrictlyAbove_shift_iff]

theorem treeEdges_shift_depth {n lower upper : ℕ} (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (depth amount : ℕ) :
    treeEdges snapshot tree upper_le_n (depth + amount) =
      (treeEdges snapshot tree upper_le_n depth).map (shiftEdgeDepth amount) := by
  induction tree generalizing depth with
  | empty => rfl
  | @node lower root upper left right ihLeft ihRight =>
      simp only [treeEdges, List.map_append]
      rw [show depth + amount + 1 = depth + 1 + amount by omega, ihLeft, ihRight]
      congr 2
      simp only [edgesAtNode, List.map_map, Function.comp_def, edgeFor, shiftEdgeDepth]
      rfl

theorem EdgeBlockUnbroken.shift_depth {n : ℕ} {edges : List (Edge n)} {block : Block n}
    (unbroken : EdgeBlockUnbroken edges block) (amount : ℕ) :
    EdgeBlockUnbroken (edges.map (shiftEdgeDepth amount)) block := by
  intro first firstMember firstIn last lastMember lastIn middle middleMember owner opposite between
  obtain ⟨oldFirst, firstOld, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨oldLast, lastOld, rfl⟩ := List.mem_map.mp lastMember
  obtain ⟨oldMiddle, middleOld, rfl⟩ := List.mem_map.mp middleMember
  exact unbroken oldFirst firstOld firstIn oldLast lastOld lastIn oldMiddle middleOld owner opposite
    ((edgeBetween_shift_iff amount oldFirst oldMiddle oldLast).mp between)

theorem EdgeBlockUnbroken.of_shift_depth {n : ℕ} {edges : List (Edge n)} {block : Block n} (amount : ℕ)
    (unbroken : EdgeBlockUnbroken (edges.map (shiftEdgeDepth amount)) block) : EdgeBlockUnbroken edges block := by
  intro first firstMember firstIn last lastMember lastIn middle middleMember owner opposite between
  exact unbroken (shiftEdgeDepth amount first) (List.mem_map.mpr ⟨first, firstMember, rfl⟩) firstIn
    (shiftEdgeDepth amount last) (List.mem_map.mpr ⟨last, lastMember, rfl⟩) lastIn
    (shiftEdgeDepth amount middle) (List.mem_map.mpr ⟨middle, middleMember, rfl⟩) owner opposite
    ((edgeBetween_shift_iff amount first middle last).mpr between)

theorem EdgeBlockUnbroken.mono {n : ℕ} {before after : List (Edge n)} {block : Block n}
    (unbroken : EdgeBlockUnbroken before block) (subset : ∀ edge ∈ after, edge ∈ before) :
    EdgeBlockUnbroken after block := by
  intro first firstMember firstIn last lastMember lastIn middle middleMember owner opposite
  exact unbroken first (subset first firstMember) firstIn last (subset last lastMember) lastIn
    middle (subset middle middleMember) owner opposite

end Splay.Accounting
