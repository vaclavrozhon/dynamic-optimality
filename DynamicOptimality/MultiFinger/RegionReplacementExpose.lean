import DynamicOptimality.MultiFinger.RegionSpecification
import DynamicOptimality.MultiFinger.TopDeletion

/-! # Isolating a consecutive marked region by two boundary splays

Splaying its predecessor and then its successor makes a consecutive
region a literal subtree at depth at most two. Its marked keys and all
its physical gaps retain their exact inorder words.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation
open ChaCha.Paper20261030.SplayAuxiliary (potential)

namespace Top

variable {α : Type*} [LinearOrder α]

theorem exposed_words (left right : MarkedTree α) (key : α)
    (ordered : (MarkedTree.node left key right).skeleton.Ordered)
    {beforeKeys afterKeys : List α}
    (word : (MarkedTree.node left key right).skeleton.inorder = beforeKeys ++ key :: afterKeys) :
    left.skeleton.inorder = beforeKeys ∧ right.skeleton.inorder = afterKeys := by
  have parts := RawDepth.node_parts ordered
  have absentLeft : key ∉ left.skeleton.inorder :=
    fun member => lt_irrefl key (parts.2.2.1 key member)
  have absentRight : key ∉ right.skeleton.inorder :=
    fun member => lt_irrefl key (parts.2.2.2 key member)
  have split := (List.append_cons_inj_of_notMem absentLeft absentRight).mp
    (show left.skeleton.inorder ++ key :: right.skeleton.inorder = beforeKeys ++ key :: afterKeys by
      simpa only [MarkedTree.skeleton, Tree.inorder, List.append_assoc, List.singleton_append] using word)
  exact ⟨split.1, split.2.2⟩

theorem expose_split (before : MarkedTree α) (beforeKeys afterKeys : List α) (key : α)
    (word : before.skeleton.inorder = beforeKeys ++ key :: afterKeys)
    (ordered : before.skeleton.Ordered) {capacity : Nat}
    (fits : before.skeleton.size ≤ capacity) :
    ∃ (left right : MarkedTree α) (count : Nat),
      MultiSplay.Auxiliary.Splay key before.skeleton
        (MarkedTree.node left key right).skeleton count ∧
      left.skeleton.inorder = beforeKeys ∧ right.skeleton.inorder = afterKeys ∧
      left.holes ++ right.holes = before.holes ∧
      Rotations before.erase (MarkedTree.node left key right).erase count ∧
      count + 2 * potential (MarkedTree.node left key right).skeleton ≤
        2 * potential before.skeleton + 6 * Nat.log 2 capacity + 1 := by
  have present : key ∈ before.skeleton.inorder := by rw [word]; simp
  obtain ⟨after, count, splay, holes, root, _, actual, bound⟩ :=
    expose before key (ordered.imp (fun less => ne_of_lt less)) present fits
  cases after with
  | hole tree => simp [MarkedTree.skeleton, Tree.rootKey] at root
  | node left pivot right =>
      have same : pivot = key := Option.some.inj root
      subst pivot
      have split := exposed_words left right key (splay.ordered_after ordered)
        (splay.inorder_eq.symm.trans word)
      exact ⟨left, right, count, splay, split.1, split.2, holes, actual, bound⟩

end Top

namespace RegionFrame

def Matches {α : Type*} (frame : RegionFrame α) (context : MarkedTree.Context α) : Prop :=
  context.keysBefore = frame.beforeKeys ∧ context.keysAfter = frame.afterKeys ∧
    context.holesBefore = frame.beforeHoles ∧ context.holesAfter = frame.afterHoles

theorem Matches.contains {α : Type*} {frame : RegionFrame α} {context : MarkedTree.Context α}
    (matching : frame.Matches context) (block : MarkedTree α) :
    frame.Contains (context.plug block) block := by
  rcases matching with ⟨first, last, front, back⟩
  simp only [Contains, MarkedTree.Context.keys_plug, MarkedTree.Context.holes_plug,
    first, last, front, back, and_self]

/-- Neither boundary belongs to the region. All opaque subtrees remain
literal, including the two end gaps of the isolated interval. -/
theorem expose {α : Type*} [LinearOrder α] (frame : RegionFrame α)
    (before oldBlock : MarkedTree α) (contained : frame.Contains before oldBlock)
    (ordered : before.skeleton.Ordered) {capacity : Nat}
    (fits : before.skeleton.size ≤ capacity) :
    ∃ (context : MarkedTree.Context α) (block : MarkedTree α) (count : Nat),
      frame.Matches context ∧ Top.contextDepth context ≤ 2 ∧
      block.skeleton.inorder = oldBlock.skeleton.inorder ∧ block.holes = oldBlock.holes ∧
      Rotations before.erase (context.plug block).erase count ∧
      count + 2 * potential (context.plug block).skeleton ≤
        2 * potential before.skeleton + 12 * Nat.log 2 capacity + 2 := by
  rcases contained with ⟨keys, holes⟩
  by_cases noBefore : frame.beforeKeys = []
  · have noBeforeHoles : frame.beforeHoles = [] := by
      simpa [noBefore] using frame.beforeCount
    cases afterEq : frame.afterKeys with
    | nil =>
        have noAfterHoles : frame.afterHoles = [] := by
          simpa [afterEq] using frame.afterCount
        refine ⟨.top, before, 0, ?_, by simp [Top.contextDepth], ?_, ?_, .refl _, ?_⟩
        · simp only [Matches, MarkedTree.Context.keysBefore, MarkedTree.Context.keysAfter,
            MarkedTree.Context.holesBefore, MarkedTree.Context.holesAfter,
            noBefore, afterEq, noBeforeHoles, noAfterHoles, and_self]
        · simpa only [noBefore, afterEq, List.nil_append, List.append_nil] using keys
        · simpa only [noBeforeHoles, noAfterHoles, List.nil_append, List.append_nil] using holes
        · change 0 + 2 * potential before.skeleton ≤ _
          omega
    | cons hi lastKeys =>
        have word : before.skeleton.inorder = oldBlock.skeleton.inorder ++ hi :: lastKeys := by
          simpa only [noBefore, afterEq, List.nil_append] using keys
        obtain ⟨block, last, count, splay, blockKeys, lastKeysEq, wholeHoles, actual, bound⟩ :=
          Top.expose_split before oldBlock.skeleton.inorder lastKeys hi word ordered fits
        have splitHoles : block.holes = oldBlock.holes ∧ last.holes = frame.afterHoles := by
          apply List.append_inj
          · simpa only [noBeforeHoles, List.nil_append] using wholeHoles.trans holes
          · rw [MarkedTree.holes_length, MarkedTree.holes_length]
            exact congrArg (· + 1) (by simpa only [Tree.length_inorder] using congrArg List.length blockKeys)
        refine ⟨.left hi last .top, block, count, ?_, by simp [Top.contextDepth],
          blockKeys, splitHoles.1, actual, ?_⟩
        · simp only [Matches, MarkedTree.Context.keysBefore, MarkedTree.Context.keysAfter,
            MarkedTree.Context.holesBefore, MarkedTree.Context.holesAfter,
            List.nil_append, noBefore, noBeforeHoles, afterEq, lastKeysEq, splitHoles.2, and_self]
        · change count + 2 * potential (MarkedTree.node block hi last).skeleton ≤ _
          omega
  · let firstKeys := frame.beforeKeys.dropLast
    let lo := frame.beforeKeys.getLast noBefore
    have prefixWord : firstKeys ++ [lo] = frame.beforeKeys := List.dropLast_append_getLast noBefore
    have word : before.skeleton.inorder =
        firstKeys ++ lo :: (oldBlock.skeleton.inorder ++ frame.afterKeys) := by
      rw [← prefixWord] at keys
      simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using keys
    obtain ⟨first, rest, firstCount, firstSplay, firstKeysEq, restKeys, firstHoles,
      firstActual, firstBound⟩ := Top.expose_split before firstKeys
        (oldBlock.skeleton.inorder ++ frame.afterKeys) lo word ordered fits
    have splitHoles : first.holes = frame.beforeHoles ∧
        rest.holes = oldBlock.holes ++ frame.afterHoles := by
      apply List.append_inj
      · simpa only [List.append_assoc] using firstHoles.trans holes
      · rw [MarkedTree.holes_length, ← Tree.length_inorder, firstKeysEq, frame.beforeCount, ← prefixWord]
        simp only [List.length_append, List.length_singleton]
    have firstPrefix : first.skeleton.inorder ++ [lo] = frame.beforeKeys := by
      rw [firstKeysEq]
      exact prefixWord
    cases afterEq : frame.afterKeys with
    | nil =>
        have noAfterHoles : frame.afterHoles = [] := by
          simpa [afterEq] using frame.afterCount
        refine ⟨.right first lo .top, rest, firstCount, ?_, by simp [Top.contextDepth],
          ?_, ?_, firstActual, ?_⟩
        · simp only [Matches, MarkedTree.Context.keysBefore, MarkedTree.Context.keysAfter,
            MarkedTree.Context.holesBefore, MarkedTree.Context.holesAfter,
            List.append_nil, firstPrefix, afterEq, noAfterHoles, splitHoles.1, and_self]
        · simpa only [afterEq, List.append_nil] using restKeys
        · simpa only [noAfterHoles, List.append_nil] using splitHoles.2
        · change firstCount + 2 * potential (MarkedTree.node first lo rest).skeleton ≤ _
          omega
    | cons hi lastKeys =>
        have nextOrdered := firstSplay.ordered_after ordered
        have restFits : rest.skeleton.size ≤ capacity := by
          have sizes := firstSplay.size_eq
          simp only [MarkedTree.skeleton, Tree.size] at sizes
          omega
        obtain ⟨block, last, secondCount, secondSplay, blockKeys, lastKeysEq, restHoles,
          secondActual, secondBound⟩ := Top.expose_split rest oldBlock.skeleton.inorder
            lastKeys hi (by simpa only [afterEq] using restKeys)
            (RawDepth.node_parts nextOrdered).2.1 restFits
        have secondHoles : block.holes = oldBlock.holes ∧ last.holes = frame.afterHoles := by
          apply List.append_inj (restHoles.trans splitHoles.2)
          rw [MarkedTree.holes_length, MarkedTree.holes_length]
          exact congrArg (· + 1) (by simpa only [Tree.length_inorder] using congrArg List.length blockKeys)
        have exchange := Top.root_potential_exchange first.skeleton first.skeleton rest.skeleton
          (MarkedTree.node block hi last).skeleton lo rfl secondSplay.size_eq
        refine ⟨.right first lo (.left hi last .top), block, firstCount + secondCount,
          ?_, by simp [Top.contextDepth], blockKeys, secondHoles.1,
          firstActual.append (secondActual.plug [.right first.erase lo]), ?_⟩
        · simp only [Matches, MarkedTree.Context.keysBefore, MarkedTree.Context.keysAfter,
            MarkedTree.Context.holesBefore, MarkedTree.Context.holesAfter,
            List.append_nil, List.nil_append, firstPrefix, afterEq, lastKeysEq,
            splitHoles.1, secondHoles.2, and_self]
        · change firstCount + secondCount +
            2 * potential (MarkedTree.node first lo (.node block hi last)).skeleton ≤ _
          simp only [MarkedTree.skeleton] at firstBound secondBound exchange ⊢
          omega

end RegionFrame

end DynamicOptimality.MultiFinger
