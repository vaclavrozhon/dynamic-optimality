import Splay.Tree.SplayStep

namespace Splay.Tree.BST

/--
A key inside the indexed interval is at depth zero exactly when it is stored
at the root.  The interval hypotheses exclude the empty-tree case.
-/
theorem hasRoot_of_depth_eq_zero {key lower upper : ℕ}
    (tree : BST lower upper) (insideLower : lower ≤ key)
    (insideUpper : key < upper) (atDepthZero : tree.depth key = 0) :
    tree.HasRoot key := by
  cases tree with
  | empty boundary =>
      omega
  | @node lower root upper left right =>
      by_cases atRoot : key = root
      · subst key
        exact ⟨left, right, rfl⟩
      · by_cases inLeft : key < root
        · rw [depth_node_of_lt_root left right inLeft] at atDepthZero
          omega
        · have inRight : root < key := by omega
          rw [depth_node_of_root_lt left right inRight] at atDepthZero
          omega

/-- A root certificate computes the named key's search depth to zero. -/
theorem depth_eq_zero_of_hasRoot {key lower upper : ℕ}
    {tree : BST lower upper} (root : tree.HasRoot key) :
    tree.depth key = 0 := by
  obtain ⟨left, right, rfl⟩ := root
  exact depth_root left right

namespace Zig

/-- The indexed interval of a zig contains its promoted key. -/
theorem key_bounds {key lower upper : ℕ}
    {before after : BST lower upper} (step : Zig key before after) :
    lower ≤ key ∧ key < upper := by
  cases step with
  | fromLeft a b c =>
      have ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      omega
  | fromRight a b c =>
      have ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      omega

/-- Before a zig, the promoted key is one level below the root. -/
theorem depth_before_eq_one {key lower upper : ℕ}
    {before after : BST lower upper} (step : Zig key before after) :
    before.depth key = 1 := by
  cases step with
  | fromLeft a b c =>
      have hb := b.lower_le_upper
      rw [depth_node_of_lt_root (.node a b) c (by omega)]
      rw [depth_root]
  | fromRight a b c =>
      have hb := b.lower_le_upper
      rw [depth_node_of_root_lt a (.node b c) (by omega)]
      rw [depth_root]

/-- After a zig, the promoted key is at the root. -/
theorem depth_after_eq_zero {key lower upper : ℕ}
    {before after : BST lower upper} (step : Zig key before after) :
    after.depth key = 0 := by
  obtain ⟨left, right, rfl⟩ := step.hasRoot_after
  exact depth_root left right

/--
Any in-range key at depth one admits the unique-orientation final zig that
promotes it to the root.
-/
theorem exists_of_depth_eq_one {key lower upper : ℕ}
    (tree : BST lower upper) (insideLower : lower ≤ key)
    (insideUpper : key < upper) (atDepthOne : tree.depth key = 1) :
    ∃ after : BST lower upper, Zig key tree after := by
  cases tree with
  | empty boundary =>
      simp [depth] at atDepthOne
  | @node lower root upper left right =>
      by_cases atRoot : key = root
      · subst key
        rw [depth_root] at atDepthOne
        omega
      · by_cases inLeft : key < root
        · have childDepth : left.depth key = 0 := by
            rw [depth_node_of_lt_root left right inLeft] at atDepthOne
            omega
          obtain ⟨a, b, rfl⟩ :=
            hasRoot_of_depth_eq_zero left insideLower inLeft childDepth
          exact
            ⟨.node a (.node b right), .fromLeft a b right⟩
        · have inRight : root < key := by omega
          have childDepth : right.depth key = 0 := by
            rw [depth_node_of_root_lt left right inRight] at atDepthOne
            omega
          obtain ⟨b, c, rfl⟩ :=
            hasRoot_of_depth_eq_zero right (by omega) insideUpper childDepth
          exact
            ⟨.node (.node left b) c, .fromRight left b c⟩

end Zig

namespace DoubleRotation

/-- The indexed interval of a double rotation contains its promoted key. -/
theorem key_bounds {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotation key before after) :
    lower ≤ key ∧ key < upper := by
  cases step with
  | zigZigLeft a b c d =>
      have ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega
  | zigZigRight a b c d =>
      have ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega
  | zigZagLeftRight a b c d =>
      have ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega
  | zigZagRightLeft a b c d =>
      have ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega

/-- Before a local double rotation, the promoted key is two levels deep. -/
theorem depth_before_eq_two {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotation key before after) :
    before.depth key = 2 := by
  cases step with
  | zigZigLeft a b c d =>
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      rw [depth_node_of_lt_root (.node (.node a b) c) d (by omega)]
      rw [depth_node_of_lt_root (.node a b) c (by omega)]
      rw [depth_root]
  | zigZigRight a b c d =>
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      rw [depth_node_of_root_lt a (.node b (.node c d)) (by omega)]
      rw [depth_node_of_root_lt b (.node c d) (by omega)]
      rw [depth_root]
  | zigZagLeftRight a b c d =>
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      rw [depth_node_of_lt_root (.node a (.node b c)) d (by omega)]
      rw [depth_node_of_root_lt a (.node b c) (by omega)]
      rw [depth_root]
  | zigZagRightLeft a b c d =>
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      rw [depth_node_of_root_lt a (.node (.node b c) d) (by omega)]
      rw [depth_node_of_lt_root (.node b c) d (by omega)]
      rw [depth_root]

/-- After a local double rotation, the promoted key is at the local root. -/
theorem depth_after_eq_zero {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotation key before after) :
    after.depth key = 0 := by
  obtain ⟨left, right, rfl⟩ := step.hasRoot_after
  exact depth_root left right

end DoubleRotation

/--
A standard double splay rotation under an arbitrary number of enclosing
search-tree nodes.

The depth is the depth of the grandparent subtree whose root is replaced.
Thus the promoted key moves from depth `depth + 2` to depth `depth` in the
whole tree.  Unlike `DoubleRotation`, this relation is not restricted to a
grandchild of the global root.
-/
inductive DoubleRotationAt :
    ℕ → ℕ → {lower upper : ℕ} → BST lower upper → BST lower upper → Prop
  | root {key lower upper : ℕ} {before after : BST lower upper}
      (step : DoubleRotation key before after) :
      DoubleRotationAt 0 key before after
  | leftContext {depth key lower root upper : ℕ}
      {before after : BST lower root}
      (step : DoubleRotationAt depth key before after)
      (right : BST (root + 1) upper) :
      DoubleRotationAt depth.succ key
        (.node before right) (.node after right)
  | rightContext {depth key lower root upper : ℕ}
      (left : BST lower root)
      {before after : BST (root + 1) upper}
      (step : DoubleRotationAt depth key before after) :
      DoubleRotationAt depth.succ key
        (.node left before) (.node left after)

namespace DoubleRotationAt

/-- A contextual double rotation can only name a key in its indexed interval. -/
theorem key_bounds {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after) :
    lower ≤ key ∧ key < upper := by
  induction step with
  | root step =>
      exact step.key_bounds
  | leftContext step right ih =>
      have hRight := right.lower_le_upper
      omega
  | rightContext left step ih =>
      have hLeft := left.lower_le_upper
      omega

/-- The named key starts exactly two levels below the contextual root. -/
theorem depth_before_eq {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after) :
    before.depth key = depth + 2 := by
  induction step with
  | root step =>
      simpa using step.depth_before_eq_two
  | leftContext step right ih =>
      rw [depth_node_of_lt_root _ right (by
        exact step.key_bounds.2)]
      rw [ih]
  | rightContext left step ih =>
      rw [depth_node_of_root_lt left _ (by
        have := step.key_bounds.1
        omega)]
      rw [ih]

/-- The named key ends at the root of the contextual subtree. -/
theorem depth_after_eq {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after) :
    after.depth key = depth := by
  induction step with
  | root step =>
      simpa using step.depth_after_eq_zero
  | leftContext step right ih =>
      rw [depth_node_of_lt_root _ right (by
        exact step.key_bounds.2)]
      rw [ih]
  | rightContext left step ih =>
      rw [depth_node_of_root_lt left _ (by
        have := step.key_bounds.1
        omega)]
      rw [ih]

/--
A contextual double splay rotation is exactly two ordinary rotations.  The
second one is at the contextual depth; the first is at that depth or one
level below it, covering both zig-zig and zig-zag orientations.
-/
theorem toTwoRotations {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after) :
    ∃ (middle : BST lower upper) (firstDepth : ℕ),
      depth ≤ firstDepth ∧
        firstDepth ≤ depth + 1 ∧
        RotationAt firstDepth before middle ∧
        RotationAt depth middle after := by
  induction step with
  | root step =>
      obtain ⟨middle, firstDepth, firstDepth_le, first, second⟩ :=
        step.toTwoRotations
      exact
        ⟨middle, firstDepth, by omega, by omega, first, second⟩
  | leftContext step right ih =>
      obtain ⟨middle, firstDepth, depth_le, firstDepth_le, first, second⟩ :=
        ih
      exact
        ⟨.node middle right, firstDepth.succ, by omega, by omega,
          .leftContext first right, .leftContext second right⟩
  | rightContext left step ih =>
      obtain ⟨middle, firstDepth, depth_le, firstDepth_le, first, second⟩ :=
        ih
      exact
        ⟨.node left middle, firstDepth.succ, by omega, by omega,
          .rightContext left first, .rightContext left second⟩

/-- A contextual double rotation preserves the number of keys. -/
theorem size_eq {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after) :
    before.size = after.size := by
  obtain ⟨middle, _, _, _, first, second⟩ := step.toTwoRotations
  exact first.size_eq.trans second.size_eq

/--
Whenever an in-range key has depth at least two, its bottom-most available
splay action is a contextual double rotation.  The construction descends
through arbitrary surrounding nodes until the key is a grandchild, then
selects the appropriate zig-zig or zig-zag orientation.
-/
theorem exists_of_two_le_depth {key lower upper : ℕ}
    (tree : BST lower upper) (insideLower : lower ≤ key)
    (insideUpper : key < upper) (two_le : 2 ≤ tree.depth key) :
    ∃ (after : BST lower upper) (depth : ℕ),
      DoubleRotationAt depth key tree after := by
  induction tree generalizing key with
  | empty boundary =>
      simp [depth] at two_le
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · subst key
        rw [depth_root] at two_le
        omega
      · by_cases inLeft : key < root
        · rw [depth_node_of_lt_root left right inLeft] at two_le
          have one_le_child : 1 ≤ left.depth key := by omega
          by_cases two_le_child : 2 ≤ left.depth key
          · obtain ⟨childAfter, contextDepth, childStep⟩ :=
              ihLeft insideLower inLeft two_le_child
            exact
              ⟨.node childAfter right, contextDepth.succ,
                .leftContext childStep right⟩
          · have atDepthOne : left.depth key = 1 := by omega
            obtain ⟨childAfter, childZig⟩ :=
              Zig.exists_of_depth_eq_one
                left insideLower inLeft atDepthOne
            cases childZig with
            | fromLeft a b c =>
                exact
                  ⟨.node a (.node b (.node c right)), 0,
                    .root (.zigZigLeft a b c right)⟩
            | fromRight a b c =>
                exact
                  ⟨.node (.node a b) (.node c right), 0,
                    .root (.zigZagLeftRight a b c right)⟩
        · have inRight : root < key := by omega
          rw [depth_node_of_root_lt left right inRight] at two_le
          have one_le_child : 1 ≤ right.depth key := by omega
          by_cases two_le_child : 2 ≤ right.depth key
          · obtain ⟨childAfter, contextDepth, childStep⟩ :=
              ihRight (by omega) insideUpper two_le_child
            exact
              ⟨.node left childAfter, contextDepth.succ,
                .rightContext left childStep⟩
          · have atDepthOne : right.depth key = 1 := by omega
            obtain ⟨childAfter, childZig⟩ :=
              Zig.exists_of_depth_eq_one
                right (by omega) insideUpper atDepthOne
            cases childZig with
            | fromLeft a b c =>
                exact
                  ⟨.node (.node left a) (.node b c), 0,
                    .root (.zigZagRightLeft left a b c)⟩
            | fromRight a b c =>
                exact
                  ⟨.node (.node (.node left a) b) c, 0,
                    .root (.zigZigRight left a b c)⟩

end DoubleRotationAt

/--
A flat finite execution of ordinary single rotations.

Every constructor records one `RotationAt`, including its own contextual
depth, while the natural-number index records the exact number of rotations.
The intermediate trees are carried by the dependent constructor, so adjacent
steps are forced to meet at the same state.
-/
inductive RotationExecution :
    ℕ → {lower upper : ℕ} → BST lower upper → BST lower upper → Prop
  | refl {lower upper : ℕ} {tree : BST lower upper} :
      RotationExecution 0 tree tree
  | step {length rotationDepth lower upper : ℕ}
      {before middle after : BST lower upper}
      (head : RotationAt rotationDepth before middle)
      (tail : RotationExecution length middle after) :
      RotationExecution length.succ before after

namespace RotationExecution

/-- A single ordinary rotation is a one-step flat execution. -/
theorem singleton {rotationDepth lower upper : ℕ}
    {before after : BST lower upper}
    (rotation : RotationAt rotationDepth before after) :
    RotationExecution 1 before after :=
  .step rotation .refl

/-- Concatenation preserves both endpoints and adds exact rotation counts. -/
theorem append {prefixLength suffixLength lower upper : ℕ}
    {before middle after : BST lower upper}
    (firstPart : RotationExecution prefixLength before middle)
    (suffix : RotationExecution suffixLength middle after) :
    RotationExecution (prefixLength + suffixLength) before after := by
  induction firstPart with
  | refl =>
      simpa using suffix
  | step head tail ih =>
      simpa [Nat.succ_add] using
        (RotationExecution.step head (ih suffix))

/-- Every flat ordinary-rotation execution preserves the number of keys. -/
theorem size_eq {length lower upper : ℕ}
    {before after : BST lower upper}
    (execution : RotationExecution length before after) :
    before.size = after.size := by
  induction execution with
  | refl =>
      rfl
  | step head tail ih =>
      exact head.size_eq.trans ih

end RotationExecution

namespace Zig

/-- A final zig flattens to exactly one ordinary root rotation. -/
theorem toRotationExecution {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : Zig key before after) :
    RotationExecution 1 before after :=
  RotationExecution.singleton (.root step.toRootRotation)

end Zig

namespace DoubleRotationAt

/-- A contextual double rotation flattens to exactly two ordinary rotations. -/
theorem toRotationExecution {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after) :
    RotationExecution 2 before after := by
  obtain ⟨middle, _, _, _, first, second⟩ := step.toTwoRotations
  exact .step first (.step second .refl)

end DoubleRotationAt

/--
One bottom-up splay step: either the final root zig or a double rotation at an
arbitrary contextual depth.
-/
inductive SplayStep (key : ℕ) :
    {lower upper : ℕ} → BST lower upper → BST lower upper → Prop
  | zig {lower upper : ℕ} {before after : BST lower upper}
      (step : Zig key before after) :
      SplayStep key before after
  | double {depth lower upper : ℕ} {before after : BST lower upper}
      (step : DoubleRotationAt depth key before after) :
      SplayStep key before after

namespace SplayStep

/-- A splay step names a key inside the tree's indexed interval. -/
theorem key_bounds {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : SplayStep key before after) :
    lower ≤ key ∧ key < upper := by
  cases step with
  | zig step =>
      exact step.key_bounds
  | double step =>
      exact step.key_bounds

/--
Every splay step is implemented by one or two rotations at explicit depths.
-/
theorem toOneOrTwoRotations {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : SplayStep key before after) :
    (∃ depth, RotationAt depth before after) ∨
      ∃ (middle : BST lower upper) (firstDepth secondDepth : ℕ),
        RotationAt firstDepth before middle ∧
          RotationAt secondDepth middle after := by
  cases step with
  | zig step =>
      exact Or.inl ⟨0, .root step.toRootRotation⟩
  | double step =>
      obtain ⟨middle, firstDepth, _, _, first, second⟩ :=
        step.toTwoRotations
      exact Or.inr ⟨middle, firstDepth, _, first, second⟩

/--
A splay step flattens to ordinary rotations, and its rotation count is exactly
the amount by which it decreases the accessed key's depth.
-/
theorem toRotationExecution {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : SplayStep key before after) :
    ∃ rotationCount : ℕ,
      RotationExecution rotationCount before after ∧
        before.depth key = rotationCount + after.depth key := by
  cases step with
  | zig step =>
      refine ⟨1, step.toRotationExecution, ?_⟩
      rw [step.depth_before_eq_one, step.depth_after_eq_zero]
  | double step =>
      refine ⟨2, step.toRotationExecution, ?_⟩
      rw [step.depth_before_eq, step.depth_after_eq]
      omega

/-- Every splay step strictly decreases the depth of its named key. -/
theorem depth_after_lt_before {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : SplayStep key before after) :
    after.depth key < before.depth key := by
  cases step with
  | zig step =>
      rw [step.depth_before_eq_one, step.depth_after_eq_zero]
      omega
  | double step =>
      rw [step.depth_before_eq, step.depth_after_eq]
      omega

/-- Every splay step preserves the number of keys. -/
theorem size_eq {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : SplayStep key before after) :
    before.size = after.size := by
  rcases step.toOneOrTwoRotations with one | two
  · obtain ⟨_, rotation⟩ := one
    exact rotation.size_eq
  · obtain ⟨middle, _, _, first, second⟩ := two
    exact first.size_eq.trans second.size_eq

/-- Every in-range non-root key admits a depth-decreasing splay step. -/
theorem exists_of_depth_pos {key lower upper : ℕ}
    (tree : BST lower upper) (insideLower : lower ≤ key)
    (insideUpper : key < upper) (depth_pos : 0 < tree.depth key) :
    ∃ after : BST lower upper, SplayStep key tree after := by
  by_cases atDepthOne : tree.depth key = 1
  · obtain ⟨after, step⟩ :=
      Zig.exists_of_depth_eq_one
        tree insideLower insideUpper atDepthOne
    exact ⟨after, .zig step⟩
  · have two_le : 2 ≤ tree.depth key := by omega
    obtain ⟨after, _, step⟩ :=
      DoubleRotationAt.exists_of_two_le_depth
        tree insideLower insideUpper two_le
    exact ⟨after, .double step⟩

end SplayStep

/--
A finite bottom-up splay execution.  It may stop only when the named key is at
the root, so the root postcondition follows from the trace itself rather than
being an unrelated external assumption.
-/
inductive SplayExecution (key : ℕ) :
    {lower upper : ℕ} → BST lower upper → BST lower upper → Prop
  | done {lower upper : ℕ} {tree : BST lower upper}
      (root : tree.HasRoot key) :
      SplayExecution key tree tree
  | next {lower upper : ℕ}
      {before middle after : BST lower upper}
      (head : SplayStep key before middle)
      (tail : SplayExecution key middle after) :
      SplayExecution key before after

namespace SplayExecution

/-- The final tree of every splay execution has the accessed key at its root. -/
theorem hasRoot_after {key lower upper : ℕ}
    {before after : BST lower upper}
    (execution : SplayExecution key before after) :
    after.HasRoot key := by
  induction execution with
  | done root =>
      exact root
  | next head tail ih =>
      exact ih

/-- A finite splay execution preserves the number of keys. -/
theorem size_eq {key lower upper : ℕ}
    {before after : BST lower upper}
    (execution : SplayExecution key before after) :
    before.size = after.size := by
  induction execution with
  | done root =>
      rfl
  | next head tail ih =>
      exact head.size_eq.trans ih

/--
Flattening a complete splay execution yields exactly as many ordinary
rotations as the accessed key's initial depth.  The final depth contributes
nothing because `SplayExecution` can terminate only at `HasRoot`.
-/
theorem toRotationExecution {key lower upper : ℕ}
    {before after : BST lower upper}
    (execution : SplayExecution key before after) :
    RotationExecution (before.depth key) before after := by
  induction execution with
  | done root =>
      rw [depth_eq_zero_of_hasRoot root]
      exact .refl
  | next head tail ih =>
      obtain ⟨rotationCount, headExecution, depth_eq⟩ :=
        head.toRotationExecution
      rw [depth_eq]
      exact headExecution.append ih

/--
Fuelled construction of a complete splay execution.  The fuel is an upper
bound on the current search depth; each recursive call is justified by the
strict depth decrease of its head step.
-/
private theorem exists_of_depth_le {key lower upper fuel : ℕ}
    (tree : BST lower upper) (insideLower : lower ≤ key)
    (insideUpper : key < upper) (depth_le : tree.depth key ≤ fuel) :
    ∃ after : BST lower upper, SplayExecution key tree after := by
  induction fuel generalizing tree with
  | zero =>
      have atDepthZero : tree.depth key = 0 := by omega
      exact
        ⟨tree, .done
          (hasRoot_of_depth_eq_zero
            tree insideLower insideUpper atDepthZero)⟩
  | succ fuel ih =>
      by_cases atDepthZero : tree.depth key = 0
      · exact
          ⟨tree, .done
            (hasRoot_of_depth_eq_zero
              tree insideLower insideUpper atDepthZero)⟩
      · have depth_pos : 0 < tree.depth key := by omega
        obtain ⟨middle, head⟩ :=
          SplayStep.exists_of_depth_pos
            tree insideLower insideUpper depth_pos
        have middleDepth_le : middle.depth key ≤ fuel := by
          have decreases := head.depth_after_lt_before
          omega
        obtain ⟨after, tail⟩ :=
          ih middle middleDepth_le
        exact ⟨after, .next head tail⟩

/--
Every key in the indexed BST interval has a finite standard bottom-up splay
execution.  Together with `hasRoot_after`, this is the total correctness
statement for the structural splay layer.
-/
theorem exists_splay {key lower upper : ℕ} (tree : BST lower upper)
    (insideLower : lower ≤ key) (insideUpper : key < upper) :
    ∃ after : BST lower upper, SplayExecution key tree after :=
  exists_of_depth_le tree insideLower insideUpper (Nat.le_refl _)

end SplayExecution

end Splay.Tree.BST
