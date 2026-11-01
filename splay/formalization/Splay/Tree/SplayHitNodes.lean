import Splay.Accounting.SplayPairingTranscript

namespace Splay.Tree.BST

/--
The value keys encountered while searching for `key`, from the root down.

For an in-range key the last entry is `key`.  This list gives persistent
identities to the internal nodes that the bottom-up splay removes from the
search path; unlike structural depths, those identities remain meaningful
after earlier rotations.
-/
def searchPath {lower upper : ℕ} : BST lower upper → ℕ → List ℕ
  | .empty _, _ => []
  | .node (root := root) left right, key =>
      root ::
        if key = root then []
        else if key < root then searchPath left key
        else searchPath right key

namespace searchPath

/-- Every key on an in-range search path belongs to the tree's index range. -/
theorem mem_bounds {lower upper key member : ℕ}
    (tree : BST lower upper) (insideLower : lower ≤ key)
    (insideUpper : key < upper)
    (memberPath : member ∈ tree.searchPath key) :
    lower ≤ member ∧ member < upper := by
  induction tree with
  | empty boundary =>
      simp [searchPath] at memberPath
  | @node lower root upper left right ihLeft ihRight =>
      simp only [searchPath, List.mem_cons] at memberPath
      rcases memberPath with rfl | memberPath
      · exact ⟨left.lower_le_upper, by
          have := right.lower_le_upper
          omega⟩
      · by_cases atRoot : key = root
        · simp [atRoot] at memberPath
        · by_cases inLeft : key < root
          · simp [atRoot, inLeft] at memberPath
            have bounds := ihLeft insideLower inLeft memberPath
            exact ⟨bounds.1, bounds.2.trans (by
              have := right.lower_le_upper
              omega)⟩
          · have inRight : root < key := by omega
            simp [atRoot, inLeft] at memberPath
            have bounds := ihRight (by omega) insideUpper memberPath
            exact ⟨left.lower_le_upper.trans (by
              exact (Nat.le_succ root).trans bounds.1), bounds.2⟩

/-- The search path to an in-range key contains no repeated internal node. -/
theorem nodup {lower upper key : ℕ}
    (tree : BST lower upper) (insideLower : lower ≤ key)
    (insideUpper : key < upper) :
    (tree.searchPath key).Nodup := by
  induction tree with
  | empty boundary =>
      simp [searchPath]
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · simp [searchPath, atRoot]
      · by_cases inLeft : key < root
        · have childNodup := ihLeft insideLower inLeft
          have rootNotMem : root ∉ left.searchPath key := by
            intro member
            have bounds := mem_bounds left insideLower inLeft member
            omega
          simpa [searchPath, atRoot, inLeft, rootNotMem] using
            List.nodup_cons.mpr ⟨rootNotMem, childNodup⟩
        · have inRight : root < key := by omega
          have childNodup := ihRight (by omega) insideUpper
          have rootNotMem : root ∉ right.searchPath key := by
            intro member
            have bounds := mem_bounds right (by omega) insideUpper member
            omega
          simpa [searchPath, atRoot, inLeft, rootNotMem] using
            List.nodup_cons.mpr ⟨rootNotMem, childNodup⟩

/-- A root certificate computes the complete search path to `[key]`. -/
theorem eq_singleton_of_hasRoot {lower upper key : ℕ}
    {tree : BST lower upper} (root : tree.HasRoot key) :
    tree.searchPath key = [key] := by
  obtain ⟨left, right, rfl⟩ := root
  simp [searchPath]

/-- An in-range search path has one more entry than the search depth. -/
theorem length_eq_depth_add_one {lower upper key : ℕ}
    (tree : BST lower upper) (insideLower : lower ≤ key)
    (insideUpper : key < upper) :
    (tree.searchPath key).length = tree.depth key + 1 := by
  induction tree with
  | empty boundary =>
      omega
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · subst key
        simp [searchPath, depth]
      · by_cases inLeft : key < root
        · rw [depth_node_of_lt_root left right inLeft]
          simp [searchPath, atRoot, inLeft,
            ihLeft insideLower inLeft]
        · have inRight : root < key := by omega
          rw [depth_node_of_root_lt left right inRight]
          simp [searchPath, atRoot, inLeft,
            ihRight (by omega) insideUpper]

/-- Searching for an in-range key visits at least that key. -/
theorem ne_nil {lower upper key : ℕ}
    (tree : BST lower upper) (insideLower : lower ≤ key)
    (insideUpper : key < upper) :
    tree.searchPath key ≠ [] := by
  intro emptyPath
  have lengthEq := length_eq_depth_add_one tree insideLower insideUpper
  rw [emptyPath] at lengthEq
  simp at lengthEq

/-- Adding a left search context appends its root to the bottom-up ancestors. -/
theorem properAncestors_leftContext {lower root upper key : ℕ}
    (inside : BST lower root) (right : BST (root + 1) upper)
    (insideLower : lower ≤ key) (keyLt : key < root) :
    ((BST.node inside right).searchPath key).dropLast.reverse =
      (inside.searchPath key).dropLast.reverse ++ [root] := by
  have pathNonempty := ne_nil inside insideLower keyLt
  cases pathEq : inside.searchPath key with
  | nil => exact (pathNonempty pathEq).elim
  | cons first rest =>
      simp [searchPath, show key ≠ root by omega, keyLt, pathEq]

/-- Adding a right search context appends its root to the bottom-up ancestors. -/
theorem properAncestors_rightContext {lower root upper key : ℕ}
    (left : BST lower root) (inside : BST (root + 1) upper)
    (rootLt : root < key) (insideUpper : key < upper) :
    ((BST.node left inside).searchPath key).dropLast.reverse =
      (inside.searchPath key).dropLast.reverse ++ [root] := by
  have pathNonempty := ne_nil inside (by omega) insideUpper
  cases pathEq : inside.searchPath key with
  | nil => exact (pathNonempty pathEq).elim
  | cons first rest =>
      simp [searchPath, show key ≠ root by omega,
        show ¬ key < root by omega, pathEq]

/-- Every bottom-up proper ancestor has the bounds of the searched subtree. -/
theorem mem_bounds_of_mem_properAncestors
    {lower upper key ancestor : ℕ}
    (tree : BST lower upper) (insideLower : lower ≤ key)
    (insideUpper : key < upper)
    (member : ancestor ∈ (tree.searchPath key).dropLast.reverse) :
    lower ≤ ancestor ∧ ancestor < upper := by
  have memberDropLast : ancestor ∈ (tree.searchPath key).dropLast := by
    simpa using member
  exact mem_bounds tree insideLower insideUpper
    ((List.dropLast_sublist _).mem memberDropLast)

end searchPath

namespace Zig

/-- A final zig deletes precisely its parent from the search path. -/
theorem exists_searchPath_parent {key lower upper : ℕ}
    {before after : BST lower upper} (step : Zig key before after) :
    ∃ parent,
      before.searchPath key = [parent, key] ∧
        after.searchPath key = [key] := by
  cases step with
  | @fromLeft lower _ demoted upper a b c =>
      have promotedLt : key < demoted := by
        have := b.lower_le_upper
        omega
      refine ⟨demoted, ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show key ≠ demoted by omega, promotedLt]
      · simp [_root_.Splay.Tree.BST.searchPath]
  | @fromRight lower demoted _ upper a b c =>
      have demotedLt : demoted < key := by
        have := b.lower_le_upper
        omega
      refine ⟨demoted, ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show key ≠ demoted by omega,
          show ¬key < demoted by omega]
      · simp [_root_.Splay.Tree.BST.searchPath]

end Zig

namespace DoubleRotation

/-- A local double rotation deletes its grandparent and parent from the path. -/
theorem exists_searchPath_hits {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotation key before after) :
    ∃ grandparent parent,
      before.searchPath key = [grandparent, parent, key] ∧
        after.searchPath key = [key] := by
  cases step with
  | @zigZigLeft lower _ second third upper a b c d =>
      have firstLtSecond : key < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      refine ⟨third, second, ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show key ≠ third by omega, show key < third by omega,
          show key ≠ second by omega, firstLtSecond]
      · simp [_root_.Splay.Tree.BST.searchPath]
  | @zigZigRight lower first second _ upper a b c d =>
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < key := by
        have := c.lower_le_upper
        omega
      refine ⟨first, second, ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show key ≠ first by omega, show ¬key < first by omega,
          show key ≠ second by omega, show ¬key < second by omega]
      · simp [_root_.Splay.Tree.BST.searchPath]
  | @zigZagLeftRight lower first _ third upper a b c d =>
      have firstLtSecond : first < key := by
        have := b.lower_le_upper
        omega
      have secondLtThird : key < third := by
        have := c.lower_le_upper
        omega
      refine ⟨third, first, ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show key ≠ third by omega, show key < third by omega,
          show key ≠ first by omega, show ¬key < first by omega]
      · simp [_root_.Splay.Tree.BST.searchPath]
  | @zigZagRightLeft lower first _ third upper a b c d =>
      have firstLtSecond : first < key := by
        have := b.lower_le_upper
        omega
      have secondLtThird : key < third := by
        have := c.lower_le_upper
        omega
      refine ⟨first, third, ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show key ≠ first by omega, show ¬key < first by omega,
          show key ≠ third by omega, show key < third by omega]
      · simp [_root_.Splay.Tree.BST.searchPath]

end DoubleRotation

namespace DoubleRotationAt

/-- A contextual double rotation preserves the prefix above its two hits. -/
theorem exists_searchPath_hits {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after) :
    ∃ (pathPrefix : List ℕ) (grandparent parent : ℕ),
      pathPrefix.length = depth ∧
        before.searchPath key = pathPrefix ++ [grandparent, parent, key] ∧
        after.searchPath key = pathPrefix ++ [key] := by
  induction step with
  | root step =>
      obtain ⟨grandparent, parent, beforeEq, afterEq⟩ :=
        step.exists_searchPath_hits
      exact ⟨[], grandparent, parent, rfl, beforeEq, afterEq⟩
  | @leftContext depth key lower root upper before after step right ih =>
      obtain ⟨pathPrefix, grandparent, parent, prefixLength,
        beforeEq, afterEq⟩ := ih
      have keyLt : key < root := step.key_bounds.2
      refine ⟨root :: pathPrefix, grandparent, parent, by simp [prefixLength],
        ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show key ≠ root by omega, keyLt, beforeEq]
      · simp [_root_.Splay.Tree.BST.searchPath,
          show key ≠ root by omega, keyLt, afterEq]
  | @rightContext depth key lower root upper left before after step ih =>
      obtain ⟨pathPrefix, grandparent, parent, prefixLength,
        beforeEq, afterEq⟩ := ih
      have rootLt : root < key := by
        have := step.key_bounds.1
        omega
      refine ⟨root :: pathPrefix, grandparent, parent, by simp [prefixLength],
        ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show key ≠ root by omega, show ¬key < root by omega, beforeEq]
      · simp [_root_.Splay.Tree.BST.searchPath,
          show key ≠ root by omega, show ¬key < root by omega, afterEq]

end DoubleRotationAt

namespace SplayExecution

/-- A complete splay names a key in the indexed interval. -/
theorem key_bounds
    {key lower upper : ℕ} {before after : BST lower upper}
    (execution : SplayExecution key before after) :
    lower ≤ key ∧ key < upper := by
  cases execution with
  | done root =>
      obtain ⟨left, right, _⟩ := root
      exact ⟨left.lower_le_upper, by
        have := right.lower_le_upper
        omega⟩
  | next head tail => exact head.key_bounds

/--
Persistent identities of all hit internal nodes, ordered from the accessed
key upward.  A complete bottom-up splay hits every proper ancestor exactly
once, so these are precisely the reversed initial search path without its
last entry `key`.
-/
def hitNodes {key lower upper : ℕ} {before after : BST lower upper}
    (_execution : SplayExecution key before after) : List ℕ :=
  (before.searchPath key).dropLast.reverse

/-- No persistent internal-node identity is hit twice in one complete splay. -/
theorem hitNodes_nodup
    {key lower upper : ℕ} {before after : BST lower upper}
    (execution : SplayExecution key before after) :
    execution.hitNodes.Nodup := by
  rw [hitNodes, List.nodup_reverse]
  exact (List.dropLast_sublist _).nodup
    (searchPath.nodup before execution.key_bounds.1 execution.key_bounds.2)

/-- The number of hit identities is exactly the initial search depth. -/
theorem length_hitNodes
    {key lower upper : ℕ} {before after : BST lower upper}
    (execution : SplayExecution key before after) :
    execution.hitNodes.length = before.depth key := by
  rw [hitNodes, List.length_reverse, List.length_dropLast,
    searchPath.length_eq_depth_add_one before
      execution.key_bounds.1 execution.key_bounds.2]
  omega

/-- After a final zig, dropping its one hit leaves the tail hit list. -/
theorem drop_one_hitNodes_of_zig
    {key lower upper : ℕ} {before after : BST lower upper}
    (step : Zig key before after) :
    ((before.searchPath key).dropLast.reverse).drop 1 =
      (after.searchPath key).dropLast.reverse := by
  obtain ⟨parent, beforeEq, afterEq⟩ := step.exists_searchPath_parent
  rw [beforeEq, afterEq]
  rfl

/-- After a double rotation, dropping its two hits leaves the tail hit list. -/
theorem drop_two_hitNodes_of_double
    {depth key lower upper : ℕ} {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after) :
    ((before.searchPath key).dropLast.reverse).drop 2 =
      (after.searchPath key).dropLast.reverse := by
  obtain ⟨pathPrefix, grandparent, parent, _, beforeEq, afterEq⟩ :=
    step.exists_searchPath_hits
  rw [beforeEq, afterEq]
  simp

end SplayExecution

end Splay.Tree.BST

namespace Splay.Accounting

open Splay.Tree.BST

namespace SplayExecutionTranscript

/-- A transcript starting with the accessed key at the root has no steps. -/
theorem kinds_eq_nil_of_hasRoot_before
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (root : before.HasRoot key) :
    kinds = [] := by
  cases transcript with
  | done => rfl
  | zig step tail transcript =>
      have rootDepth := depth_eq_zero_of_hasRoot root
      have stepDepth := step.depth_before_eq_one
      omega
  | zigZig step orientation tail transcript =>
      have rootDepth := depth_eq_zero_of_hasRoot root
      have stepDepth := step.depth_before_eq
      omega
  | zigZag step orientation tail transcript =>
      have rootDepth := depth_eq_zero_of_hasRoot root
      have stepDepth := step.depth_before_eq
      omega

/-- Number of persistent search-path identities consumed by one splay step. -/
def stepHitCount : SplayStepKind → ℕ
  | .zig => 1
  | .zigZig => 2
  | .zigZag => 2

/-- Total number of hit internal nodes encoded by a kind list. -/
def totalHitCount : List SplayStepKind → ℕ
  | [] => 0
  | kind :: kinds => stepHitCount kind + totalHitCount kinds

/--
Partition the persistent hit identities according to the chronological splay
steps and retain exactly the two-node chunks belonging to zig-zigs.
-/
def zigZigHitGroups : List SplayStepKind → List ℕ → List (List ℕ)
  | [], _ => []
  | .zig :: kinds, remaining => zigZigHitGroups kinds (remaining.drop 1)
  | .zigZig :: kinds, remaining =>
      remaining.take 2 :: zigZigHitGroups kinds (remaining.drop 2)
  | .zigZag :: kinds, remaining => zigZigHitGroups kinds (remaining.drop 2)

/-- The retained zig-zig chunks are a sublist of the supplied hit identities. -/
theorem flatten_zigZigHitGroups_sublist
    (kinds : List SplayStepKind) (remaining : List ℕ) :
    (zigZigHitGroups kinds remaining).flatten.Sublist remaining := by
  induction kinds generalizing remaining with
  | nil => simp [zigZigHitGroups]
  | cons kind kinds ih =>
      cases kind with
      | zig =>
          exact (ih (remaining.drop 1)).trans (List.drop_sublist 1 remaining)
      | zigZig =>
          have combined :=
            (List.Sublist.refl (remaining.take 2)).append
              (ih (remaining.drop 2))
          simpa [zigZigHitGroups, List.take_append_drop] using combined
      | zigZag =>
          exact (ih (remaining.drop 2)).trans (List.drop_sublist 2 remaining)

/-- Every retained group has two nodes when the supplied path is long enough. -/
theorem zigZigHitGroups_forall_length_two
    (kinds : List SplayStepKind) (remaining : List ℕ)
    (enough : totalHitCount kinds ≤ remaining.length) :
    ∀ group ∈ zigZigHitGroups kinds remaining, group.length = 2 := by
  induction kinds generalizing remaining with
  | nil => simp [zigZigHitGroups]
  | cons kind kinds ih =>
      cases kind with
      | zig =>
          apply ih (remaining.drop 1)
          change 1 + totalHitCount kinds ≤ remaining.length at enough
          rw [List.length_drop]
          omega
      | zigZig =>
          change 2 + totalHitCount kinds ≤ remaining.length at enough
          have twoLe : 2 ≤ remaining.length := by
            omega
          have tailEnough :
              totalHitCount kinds ≤ (remaining.drop 2).length := by
            simp only [List.length_drop]
            omega
          intro group member
          simp only [zigZigHitGroups, List.mem_cons] at member
          rcases member with rfl | member
          · simp [List.length_take, Nat.min_eq_left twoLe]
          · exact ih (remaining.drop 2) tailEnough group member
      | zigZag =>
          apply ih (remaining.drop 2)
          change 2 + totalHitCount kinds ≤ remaining.length at enough
          simp only [List.length_drop]
          omega

/-- There is one retained support group for every listed zig-zig. -/
theorem length_zigZigHitGroups
    (kinds : List SplayStepKind) (remaining : List ℕ) :
    (zigZigHitGroups kinds remaining).length = kinds.count .zigZig := by
  induction kinds generalizing remaining with
  | nil => simp [zigZigHitGroups]
  | cons kind kinds ih =>
      cases kind <;> simp [zigZigHitGroups, ih]

/-- A legal transcript consumes exactly the accessed key's initial depth. -/
theorem totalHitCount_eq_depth
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    totalHitCount kinds = before.depth key := by
  induction transcript with
  | done root =>
      simp [totalHitCount, depth_eq_zero_of_hasRoot root]
  | zig step tail tailTranscript ih =>
      simp only [totalHitCount, stepHitCount]
      rw [ih, step.depth_after_eq_zero, step.depth_before_eq_one]
  | zigZig step orientation tail tailTranscript ih =>
      simp only [totalHitCount, stepHitCount]
      rw [ih, step.depth_before_eq, step.depth_after_eq]
      omega
  | zigZag step orientation tail tailTranscript ih =>
      simp only [totalHitCount, stepHitCount]
      rw [ih, step.depth_before_eq, step.depth_after_eq]
      omega

/-- The canonical zig-zig support groups of one concrete execution. -/
def hitGroups
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (_transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    List (List ℕ) :=
  zigZigHitGroups kinds execution.hitNodes

/-- Zig-zig hit identities form a sublist of all identities hit by the splay. -/
theorem flatten_hitGroups_sublist_hitNodes
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    transcript.hitGroups.flatten.Sublist execution.hitNodes :=
  flatten_zigZigHitGroups_sublist kinds execution.hitNodes

/--
The persistent internal-node supports of distinct zig-zigs are disjoint.
This is the node-level content used by the manuscript's
`pairings-in-parallel` argument.
-/
theorem flatten_zigZigHitGroups_nodup
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    transcript.hitGroups.flatten.Nodup :=
  transcript.flatten_hitGroups_sublist_hitNodes.nodup
    execution.hitNodes_nodup

/-- Distinct zig-zigs have disjoint persistent two-node supports. -/
theorem hitGroups_pairwise_disjoint
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    transcript.hitGroups.Pairwise List.Disjoint :=
  (List.nodup_flatten.mp transcript.flatten_zigZigHitGroups_nodup).2

/-- Every concrete zig-zig support contains exactly its two hit nodes. -/
theorem hitGroups_forall_length_two
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    ∀ group ∈ transcript.hitGroups, group.length = 2 := by
  apply zigZigHitGroups_forall_length_two
  rw [transcript.totalHitCount_eq_depth, execution.length_hitNodes]

/-- The support-group list has exactly the transcript's zig-zig count. -/
theorem length_hitGroups
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    transcript.hitGroups.length = zigZig := by
  rw [hitGroups, length_zigZigHitGroups, transcript.count_zigZig]

end SplayExecutionTranscript

/--
A list of heap children selected from one zig-zig support.  `attachment`
names the unique internal node at which the child's original light edge was
attached.  This is the precise incidence premise used in the manuscript's
one-line proof of `pairings-in-parallel`.
-/
def SupportedHeapChildren {HeapChild InternalNode : Type*}
    (attachment : HeapChild → InternalNode)
    (support : List InternalNode) (children : List HeapChild) : Prop :=
  children.Nodup ∧
    ∀ child ∈ children, attachment child ∈ support

namespace SupportedHeapChildren

/-- Membership in selected children maps to membership in the hit support. -/
theorem attachment_mem_flatten
    {HeapChild InternalNode : Type*}
    {attachment : HeapChild → InternalNode}
    {supports : List (List InternalNode)}
    {selections : List (List HeapChild)}
    (aligned :
      List.Forall₂ (SupportedHeapChildren attachment)
        supports selections)
    {child : HeapChild} (member : child ∈ selections.flatten) :
    attachment child ∈ supports.flatten := by
  induction aligned with
  | nil => simp at member
  | @cons support selection supports selections selected rest ih =>
      simp only [List.flatten_cons, List.mem_append] at member ⊢
      rcases member with headMember | tailMember
      · exact Or.inl (selected.2 child headMember)
      · exact Or.inr (ih tailMember)

/--
Selections supported by pairwise-disjoint hit-node groups are jointly
disjoint.  In particular, taking a two-element winner/loser selection for
each zig-zig proves that no two pairings in the same phase share a heap
child.
-/
theorem flatten_nodup
    {HeapChild InternalNode : Type*}
    {attachment : HeapChild → InternalNode}
    {supports : List (List InternalNode)}
    {selections : List (List HeapChild)}
    (supportsNodup : supports.flatten.Nodup)
    (aligned :
      List.Forall₂ (SupportedHeapChildren attachment)
        supports selections) :
    selections.flatten.Nodup := by
  induction aligned with
  | nil => simp
  | @cons support selection supports selections selected rest ih =>
      simp only [List.flatten_cons] at supportsNodup ⊢
      have supportFacts := List.nodup_append.mp supportsNodup
      apply List.nodup_append.mpr
      refine ⟨selected.1, ih supportFacts.2.1, ?_⟩
      intro child childHead other childTail equal
      subst other
      have headAttachment := selected.2 child childHead
      have tailAttachment := attachment_mem_flatten rest childTail
      exact supportFacts.2.2
        (attachment child) headAttachment
        (attachment child) tailAttachment rfl

end SupportedHeapChildren

end Splay.Accounting
