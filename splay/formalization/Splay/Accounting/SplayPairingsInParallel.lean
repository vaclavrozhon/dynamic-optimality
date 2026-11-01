import Splay.Tree.SplayHitNodes
import Splay.Accounting.PairingHeapChildEndpoints

namespace Splay.Accounting

open Splay.Lazy.Canonical
open Splay.Rank
open Splay.Tree.BST

/-- The two persistent internal-node identities hit by a double rotation. -/
def zigZigHitSupport {lower upper : ℕ}
    (tree : BST lower upper) (key depth : ℕ) : List ℕ :=
  (tree.searchPath key).drop depth |>.take 2

/--
The local top-down names of a double rotation are the same two persistent
identities as the next bottom-up chunk of the complete splay.
-/
theorem DoubleRotationAt.mem_zigZigHitSupport_iff_mem_take_properAncestors
    {depth key lower upper node : ℕ} {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after) :
    node ∈ zigZigHitSupport before key depth ↔
      node ∈ ((before.searchPath key).dropLast.reverse).take 2 := by
  obtain ⟨pathPrefix, grandparent, parent, prefixLength,
    beforeEq, _⟩ := step.exists_searchPath_hits
  unfold zigZigHitSupport
  rw [beforeEq]
  simp [prefixLength, or_comm]

/-- A heap child is attached, in the pre-rotation tree, at a named hit node. -/
def HeapChildSupportedAt {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (treeDepth : ℕ)
    (support : List ℕ) (child : External n) : Prop :=
  ∃ edge : Edge n,
    edge ∈ treeEdges snapshot tree upper_le_n treeDepth ∧
      edge.child = child ∧ edge.attachmentKey ∈ support

namespace HeapChildSupportedAt

/-- A supported child remains supported when a left tree context is added. -/
theorem leftContext
    {n lower root upper : ℕ} {snapshot : Snapshot n}
    {left : BST lower root} (right : BST (root + 1) upper)
    {root_le_n : root ≤ n} {upper_le_n : upper ≤ n}
    {treeDepth : ℕ} {support : List ℕ} {child : External n}
    (supported :
      HeapChildSupportedAt snapshot left root_le_n
        (treeDepth + 1) support child) :
    HeapChildSupportedAt snapshot (.node left right) upper_le_n
      treeDepth support child := by
  obtain ⟨edge, member, childEq, attachment⟩ := supported
  refine ⟨edge, ?_, childEq, attachment⟩
  simp only [treeEdges, List.mem_append]
  exact Or.inl (Or.inr member)

/-- A supported child remains supported when a right tree context is added. -/
theorem rightContext
    {n lower root upper : ℕ} {snapshot : Snapshot n}
    (left : BST lower root) {right : BST (root + 1) upper}
    {upper_le_n : upper ≤ n}
    {treeDepth : ℕ} {support : List ℕ} {child : External n}
    (supported :
      HeapChildSupportedAt snapshot right upper_le_n
        (treeDepth + 1) support child) :
    HeapChildSupportedAt snapshot (.node left right) upper_le_n
      treeDepth support child := by
  obtain ⟨edge, member, childEq, attachment⟩ := supported
  refine ⟨edge, ?_, childEq, attachment⟩
  simp only [treeEdges, List.mem_append]
  exact Or.inr member

end HeapChildSupportedAt

namespace DoubleRotationAt

/--
A bottom-up double rotation leaves every canonical edge attached to a still
unhit search ancestor unchanged.  The attachment depth is unchanged as well:
all such nodes lie in the context above the rotated three-node fragment.
-/
theorem mem_treeEdges_before_of_after_of_attachment_properAncestor
    {n depth key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after)
    (upper_le_n : upper ≤ n) (treeDepth : ℕ)
    {edge : Edge n}
    (edgeAfter :
      edge ∈ treeEdges snapshot after upper_le_n treeDepth)
    (attachment :
      edge.attachmentKey ∈ (after.searchPath key).dropLast.reverse) :
    edge ∈ treeEdges snapshot before upper_le_n treeDepth := by
  induction step generalizing treeDepth edge with
  | root step =>
      have pathEq := searchPath.eq_singleton_of_hasRoot step.hasRoot_after
      rw [pathEq] at attachment
      simp at attachment
  | @leftContext depth key lower root upper before after step right ih =>
      have keyBounds := step.key_bounds
      have rightBounds := right.lower_le_upper
      have root_le_n : root ≤ n := by omega
      have properEq :=
        searchPath.properAncestors_leftContext after right
          keyBounds.1 keyBounds.2
      rw [properEq] at attachment
      simp only [List.mem_append, List.mem_singleton] at attachment
      rw [treeEdges] at edgeAfter ⊢
      rcases List.mem_append.mp edgeAfter with edgePrefix | edgeRight
      · rcases List.mem_append.mp edgePrefix with edgeLocal | edgeInside
        · have localEq :
              edgesAtNode snapshot {
                lower := lower
                root := root
                upper := upper
                left := after
                right := right
                upper_le_n := upper_le_n
              } treeDepth =
              edgesAtNode snapshot {
                lower := lower
                root := root
                upper := upper
                left := before
                right := right
                upper_le_n := upper_le_n
              } treeDepth := by
                rfl
          rw [localEq] at edgeLocal
          apply List.mem_append.mpr
          apply Or.inl
          apply List.mem_append.mpr
          exact Or.inl edgeLocal
        · have edgeBounds :=
            mem_treeEdges_attachmentKey_bounds snapshot after root_le_n
              edgeInside
          have attachmentInside :
              edge.attachmentKey ∈
                (after.searchPath key).dropLast.reverse := by
            rcases attachment with attachmentInside | attachmentRoot
            · exact attachmentInside
            · omega
          apply List.mem_append.mpr
          apply Or.inl
          apply List.mem_append.mpr
          exact Or.inr
            (ih root_le_n (treeDepth + 1) edgeInside attachmentInside)
      · have edgeBounds :=
          mem_treeEdges_attachmentKey_bounds snapshot right upper_le_n
            edgeRight
        rcases attachment with attachmentInside | attachmentRoot
        · have ancestorBounds :=
            searchPath.mem_bounds_of_mem_properAncestors after
              keyBounds.1 keyBounds.2 attachmentInside
          omega
        · omega
  | @rightContext depth key lower root upper left before after step ih =>
      have keyBounds := step.key_bounds
      have leftBounds := left.lower_le_upper
      have rootLtKey : root < key := by omega
      have properEq :=
        searchPath.properAncestors_rightContext left after
          rootLtKey keyBounds.2
      rw [properEq] at attachment
      simp only [List.mem_append, List.mem_singleton] at attachment
      rw [treeEdges] at edgeAfter ⊢
      rcases List.mem_append.mp edgeAfter with edgePrefix | edgeInside
      · rcases List.mem_append.mp edgePrefix with edgeLocal | edgeLeft
        · have localEq :
              edgesAtNode snapshot {
                lower := lower
                root := root
                upper := upper
                left := left
                right := after
                upper_le_n := upper_le_n
              } treeDepth =
              edgesAtNode snapshot {
                lower := lower
                root := root
                upper := upper
                left := left
                right := before
                upper_le_n := upper_le_n
              } treeDepth := by
                rfl
          rw [localEq] at edgeLocal
          apply List.mem_append.mpr
          apply Or.inl
          apply List.mem_append.mpr
          exact Or.inl edgeLocal
        · have edgeBounds :=
            mem_treeEdges_attachmentKey_bounds snapshot left (by omega)
              edgeLeft
          rcases attachment with attachmentInside | attachmentRoot
          · have ancestorBounds :=
              searchPath.mem_bounds_of_mem_properAncestors after
                keyBounds.1 keyBounds.2 attachmentInside
            omega
          · omega
      · have edgeBounds :=
          mem_treeEdges_attachmentKey_bounds snapshot after upper_le_n
            edgeInside
        have attachmentInside :
            edge.attachmentKey ∈
              (after.searchPath key).dropLast.reverse := by
          rcases attachment with attachmentInside | attachmentRoot
          · exact attachmentInside
          · omega
        apply List.mem_append.mpr
        exact Or.inr
          (ih upper_le_n (treeDepth + 1) edgeInside attachmentInside)

end DoubleRotationAt

/-- A whole phase selection, with its incoming edges witnessed in one tree. -/
def HeapChildrenSupportedIn {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (support : List ℕ)
    (children : List (External n)) : Prop :=
  children.length = 2 ∧ children.Nodup ∧
    ∀ child ∈ children,
      HeapChildSupportedAt snapshot tree upper_le_n 0 support child

namespace HeapChildrenSupportedIn

/-- A selected child in the flattened batches has one witnessed original edge. -/
theorem exists_edge_of_mem_flatten
    {n lower upper : ℕ} {snapshot : Snapshot n}
    {tree : BST lower upper} {upper_le_n : upper ≤ n}
    {supports : List (List ℕ)}
    {selections : List (List (External n))}
    (aligned :
      List.Forall₂
        (HeapChildrenSupportedIn snapshot tree upper_le_n)
        supports selections)
    {child : External n} (member : child ∈ selections.flatten) :
    ∃ edge : Edge n,
      edge ∈ treeEdges snapshot tree upper_le_n 0 ∧
        edge.child = child ∧ edge.attachmentKey ∈ supports.flatten := by
  induction aligned with
  | nil => simp at member
  | @cons support children supports selections selected rest ih =>
      simp only [List.flatten_cons, List.mem_append] at member ⊢
      rcases member with childHead | childTail
      · obtain ⟨edge, edgeMember, childEq, attachmentMember⟩ :=
          selected.2.2 child childHead
        exact ⟨edge, edgeMember, childEq, Or.inl attachmentMember⟩
      · obtain ⟨edge, edgeMember, childEq, attachmentMember⟩ :=
          ih childTail
        exact ⟨edge, edgeMember, childEq, Or.inr attachmentMember⟩

/-- Disjoint original attachment supports force all selected children apart. -/
theorem flatten_nodup
    {n lower upper : ℕ} {snapshot : Snapshot n}
    {tree : BST lower upper} {upper_le_n : upper ≤ n}
    {supports : List (List ℕ)}
    {selections : List (List (External n))}
    (supportsNodup : supports.flatten.Nodup)
    (aligned :
      List.Forall₂
        (HeapChildrenSupportedIn snapshot tree upper_le_n)
        supports selections) :
    selections.flatten.Nodup := by
  induction aligned with
  | nil => simp
  | @cons support children supports selections selected rest ih =>
      simp only [List.flatten_cons] at supportsNodup ⊢
      have supportFacts := List.nodup_append.mp supportsNodup
      apply List.nodup_append.mpr
      refine ⟨selected.2.1, ih supportFacts.2.1, ?_⟩
      intro child childHead other childTail equal
      subst other
      obtain ⟨headEdge, headEdgeMember, headChild, headAttachment⟩ :=
        selected.2.2 child childHead
      obtain ⟨tailEdge, tailEdgeMember, tailChild, tailAttachment⟩ :=
        exists_edge_of_mem_flatten rest childTail
      have childrenNodup :=
        treeChildren_nodup snapshot tree upper_le_n 0
      have edgeEq : headEdge = tailEdge :=
        List.inj_on_of_nodup_map childrenNodup
          headEdgeMember tailEdgeMember (headChild.trans tailChild.symm)
      have attachmentEq :
          headEdge.attachmentKey = tailEdge.attachmentKey :=
        congrArg Edge.attachmentKey edgeEq
      exact supportFacts.2.2
        headEdge.attachmentKey headAttachment
        tailEdge.attachmentKey tailAttachment attachmentEq

/-- Transport all still-unhit phase selections backwards through one double rotation. -/
theorem pullback_double
    {n depth key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    (step : DoubleRotationAt depth key before after)
    (upper_le_n : upper ≤ n)
    {supports : List (List ℕ)}
    {selections : List (List (External n))}
    (supportAncestors :
      ∀ support ∈ supports, ∀ attachment ∈ support,
        attachment ∈ (after.searchPath key).dropLast.reverse)
    (aligned :
      List.Forall₂
        (HeapChildrenSupportedIn snapshot after upper_le_n)
        supports selections) :
    List.Forall₂
      (HeapChildrenSupportedIn snapshot before upper_le_n)
      supports selections := by
  induction aligned with
  | nil => exact .nil
  | @cons support children supports selections selected rest ih =>
      apply List.Forall₂.cons
      · refine ⟨selected.1, selected.2.1, ?_⟩
        intro child childMember
        obtain ⟨edge, edgeMember, childEq, attachmentMember⟩ :=
          selected.2.2 child childMember
        refine ⟨edge, ?_, childEq, attachmentMember⟩
        exact
          Splay.Accounting.DoubleRotationAt.mem_treeEdges_before_of_after_of_attachment_properAncestor
            step upper_le_n 0 edgeMember
            (supportAncestors support (by simp) edge.attachmentKey
              attachmentMember)
      · apply ih
        intro tailSupport tailSupportMember attachment attachmentMember
        exact supportAncestors tailSupport (by simp [tailSupportMember])
          attachment attachmentMember

end HeapChildrenSupportedIn

namespace ZigZigPairingEndpointsAt

/-- The key named by a zig-zig endpoint witness lies in its BST interval. -/
theorem key_bounds
    {n : ℕ} {snapshot : Snapshot n} {phase : PairingPhase}
    {depth key lower upper : ℕ} {before after : BST lower upper}
    {winner loser : External n}
    (endpoints :
      ZigZigPairingEndpointsAt snapshot phase
        (depth := depth) (key := key) before after winner loser) :
    lower ≤ key ∧ key < upper := by
  induction endpoints with
  | zigZigLeft a b c d upper_le_n phase =>
      have _ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega
  | zigZigRight a b c d upper_le_n second_le_n phase =>
      have _ha := a.lower_le_upper
      have _hb := b.lower_le_upper
      have _hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega
  | leftContext inside right ih =>
      have := right.lower_le_upper
      exact ⟨ih.1, ih.2.trans (by omega)⟩
  | rightContext left inside ih =>
      have := left.lower_le_upper
      exact ⟨(by omega), ih.2⟩

/-- Adding a left search context preserves the two-node hit support. -/
theorem zigZigHitSupport_leftContext
    {lower root upper key depth : ℕ}
    (inside : BST lower root) (right : BST (root + 1) upper)
    (keyLt : key < root) :
    zigZigHitSupport (.node inside right) key depth.succ =
      zigZigHitSupport inside key depth := by
  simp [zigZigHitSupport, _root_.Splay.Tree.BST.searchPath,
    show key ≠ root by omega, keyLt]

/-- Adding a right search context preserves the two-node hit support. -/
theorem zigZigHitSupport_rightContext
    {lower root upper key depth : ℕ}
    (left : BST lower root) (inside : BST (root + 1) upper)
    (rootLt : root < key) :
    zigZigHitSupport (.node left inside) key depth.succ =
      zigZigHitSupport inside key depth := by
  simp [zigZigHitSupport, _root_.Splay.Tree.BST.searchPath,
    show key ≠ root by omega, show ¬key < root by omega]

private theorem zigZigLeft_branch_supported
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (rankZero : snapshot.rank ⟨2 * first + 1, by
      have _ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega⟩ = 0)
    (branch : TernaryBranch) (treeDepth : ℕ) :
    let before : BST lower upper :=
      .node (.node (.node a b) c) d
    let endpointNode : AtNode n := {
      lower := second + 1
      root := third
      upper := upper
      left := c
      right := d
      upper_le_n := upper_le_n
    }
    HeapChildSupportedAt snapshot before upper_le_n treeDepth
      (zigZigHitSupport before first 0)
      (endpointNode.branchMin snapshot branch) := by
  let before : BST lower upper :=
    .node (.node (.node a b) c) d
  let endpointNode : AtNode n := {
    lower := second + 1
    root := third
    upper := upper
    left := c
    right := d
    upper_le_n := upper_le_n
  }
  let upperNode : AtNode n := {
    lower := lower
    root := third
    upper := upper
    left := .node (.node a b) c
    right := d
    upper_le_n := upper_le_n
  }
  have third_le_n : third ≤ n := by
    have := d.lower_le_upper
    omega
  let lowerNode : AtNode n := {
    lower := lower
    root := second
    upper := third
    left := .node a b
    right := c
    upper_le_n := third_le_n
  }
  let accessed : External n := ⟨2 * first + 1, by
    have ha := a.lower_le_upper
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega⟩
  have accessedUpperInside :
      upperNode.wholeLower ≤ accessed ∧
        accessed ≤ upperNode.wholeUpper := by
    change 2 * lower ≤ 2 * first + 1 ∧
      2 * first + 1 ≤ 2 * upper
    have ha := a.lower_le_upper
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have upperHeavy : upperNode.heavyBranch snapshot = .left := by
    apply upperNode.heavyBranch_eq_of_rank_eq_zero
      snapshot .left accessed rankZero accessedUpperInside
    change 2 * first + 1 ≤ 2 * third
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    omega
  have accessedLowerInside :
      lowerNode.wholeLower ≤ accessed ∧
        accessed ≤ lowerNode.wholeUpper := by
    change 2 * lower ≤ 2 * first + 1 ∧
      2 * first + 1 ≤ 2 * third
    have ha := a.lower_le_upper
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    omega
  have lowerHeavy : lowerNode.heavyBranch snapshot = .left := by
    apply lowerNode.heavyBranch_eq_of_rank_eq_zero
      snapshot .left accessed rankZero accessedLowerInside
    change 2 * first + 1 ≤ 2 * second
    have hb := b.lower_le_upper
    omega
  cases branch with
  | left =>
      let edge := edgeFor snapshot lowerNode (treeDepth + 1) .right
      have light : TernaryBranch.right ≠ lowerNode.heavyBranch snapshot := by
        rw [lowerHeavy]
        decide
      have localMember :
          edge ∈ edgesAtNode snapshot lowerNode (treeDepth + 1) := by
        simp only [edgesAtNode, List.mem_map]
        exact ⟨.right,
          (mem_lightBranches_iff snapshot lowerNode .right).2 light, rfl⟩
      have member : edge ∈ treeEdges snapshot before upper_le_n treeDepth := by
        have literalMember :
            edge ∈ edgesAtNode snapshot {
              lower := lower
              root := second
              upper := third
              left := .node a b
              right := c
              upper_le_n := by omega
            } (treeDepth + 1) := by
          simpa only [lowerNode] using localMember
        simp only [before, treeEdges, List.mem_append]
        aesop
      have childEq : edge.child = endpointNode.branchMin snapshot .left := by
        change lowerNode.branchMin snapshot .right =
          endpointNode.branchMin snapshot .left
        unfold AtNode.branchMin
        have lowerEq :
            lowerNode.branchLower .right =
              endpointNode.branchLower .left := by
          apply Fin.ext
          simp [AtNode.branchLower, AtNode.wholeLower, lowerNode,
            endpointNode]
          omega
        have upperEq :
            lowerNode.branchUpper .right =
              endpointNode.branchUpper .left := by
          apply Fin.ext
          simp [AtNode.branchUpper, AtNode.wholeUpper, lowerNode,
            endpointNode]
        cases lowerEq
        cases upperEq
        rfl
      refine ⟨edge, member, childEq, ?_⟩
      change second ∈ zigZigHitSupport before first 0
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      simp [zigZigHitSupport, before, _root_.Splay.Tree.BST.searchPath,
        show first ≠ third by omega, show first < third by omega,
        show first ≠ second by omega, firstLtSecond]
  | middle =>
      let edge := edgeFor snapshot upperNode treeDepth .middle
      have light : TernaryBranch.middle ≠ upperNode.heavyBranch snapshot := by
        rw [upperHeavy]
        decide
      have localMember : edge ∈ edgesAtNode snapshot upperNode treeDepth := by
        simp only [edgesAtNode, List.mem_map]
        exact ⟨.middle,
          (mem_lightBranches_iff snapshot upperNode .middle).2 light, rfl⟩
      have member : edge ∈ treeEdges snapshot before upper_le_n treeDepth := by
        simp only [before, treeEdges, List.mem_append]
        exact Or.inl (Or.inl localMember)
      refine ⟨edge, member, rfl, ?_⟩
      change third ∈ zigZigHitSupport before first 0
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      simp [zigZigHitSupport, before, _root_.Splay.Tree.BST.searchPath,
        show first ≠ third by omega, show first < third by omega,
        show first ≠ second by omega, firstLtSecond]
  | right =>
      let edge := edgeFor snapshot upperNode treeDepth .right
      have light : TernaryBranch.right ≠ upperNode.heavyBranch snapshot := by
        rw [upperHeavy]
        decide
      have localMember : edge ∈ edgesAtNode snapshot upperNode treeDepth := by
        simp only [edgesAtNode, List.mem_map]
        exact ⟨.right,
          (mem_lightBranches_iff snapshot upperNode .right).2 light, rfl⟩
      have member : edge ∈ treeEdges snapshot before upper_le_n treeDepth := by
        simp only [before, treeEdges, List.mem_append]
        exact Or.inl (Or.inl localMember)
      refine ⟨edge, member, rfl, ?_⟩
      change third ∈ zigZigHitSupport before first 0
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      simp [zigZigHitSupport, before, _root_.Splay.Tree.BST.searchPath,
        show first ≠ third by omega, show first < third by omega,
        show first ≠ second by omega, firstLtSecond]

private theorem zigZigRight_branch_supported
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (rankZero : snapshot.rank ⟨2 * third + 1, by
      have _ha := a.lower_le_upper
      have _hb := b.lower_le_upper
      have _hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega⟩ = 0)
    (branch : TernaryBranch) (treeDepth : ℕ) :
    let before : BST lower upper :=
      .node a (.node b (.node c d))
    let endpointNode : AtNode n := {
      lower := lower
      root := first
      upper := second
      left := a
      right := b
      upper_le_n := by
        have hc := c.lower_le_upper
        have hd := d.lower_le_upper
        omega
    }
    HeapChildSupportedAt snapshot before upper_le_n treeDepth
      (zigZigHitSupport before third 0)
      (endpointNode.branchMin snapshot branch) := by
  let before : BST lower upper :=
    .node a (.node b (.node c d))
  have second_le_n : second ≤ n := by
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  let endpointNode : AtNode n := {
    lower := lower
    root := first
    upper := second
    left := a
    right := b
    upper_le_n := second_le_n
  }
  let upperNode : AtNode n := {
    lower := lower
    root := first
    upper := upper
    left := a
    right := .node b (.node c d)
    upper_le_n := upper_le_n
  }
  let lowerNode : AtNode n := {
    lower := first + 1
    root := second
    upper := upper
    left := b
    right := .node c d
    upper_le_n := upper_le_n
  }
  let accessed : External n := ⟨2 * third + 1, by
    have ha := a.lower_le_upper
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega⟩
  have accessedUpperInside :
      upperNode.wholeLower ≤ accessed ∧
        accessed ≤ upperNode.wholeUpper := by
    change 2 * lower ≤ 2 * third + 1 ∧
      2 * third + 1 ≤ 2 * upper
    have ha := a.lower_le_upper
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have upperHeavy : upperNode.heavyBranch snapshot = .right := by
    apply upperNode.heavyBranch_eq_of_rank_eq_zero
      snapshot .right accessed rankZero accessedUpperInside
    change 2 * first + 2 ≤ 2 * third + 1
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    omega
  have accessedLowerInside :
      lowerNode.wholeLower ≤ accessed ∧
        accessed ≤ lowerNode.wholeUpper := by
    change 2 * (first + 1) ≤ 2 * third + 1 ∧
      2 * third + 1 ≤ 2 * upper
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have lowerHeavy : lowerNode.heavyBranch snapshot = .right := by
    apply lowerNode.heavyBranch_eq_of_rank_eq_zero
      snapshot .right accessed rankZero accessedLowerInside
    change 2 * second + 2 ≤ 2 * third + 1
    have hc := c.lower_le_upper
    omega
  cases branch with
  | left =>
      let edge := edgeFor snapshot upperNode treeDepth .left
      have light : TernaryBranch.left ≠ upperNode.heavyBranch snapshot := by
        rw [upperHeavy]
        decide
      have localMember : edge ∈ edgesAtNode snapshot upperNode treeDepth := by
        simp only [edgesAtNode, List.mem_map]
        exact ⟨.left,
          (mem_lightBranches_iff snapshot upperNode .left).2 light, rfl⟩
      have member : edge ∈ treeEdges snapshot before upper_le_n treeDepth := by
        simp only [before, treeEdges, List.mem_append]
        exact Or.inl (Or.inl localMember)
      refine ⟨edge, member, rfl, ?_⟩
      change first ∈ zigZigHitSupport before third 0
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      simp [zigZigHitSupport, before, _root_.Splay.Tree.BST.searchPath,
        show third ≠ first by omega, show ¬third < first by omega,
        show third ≠ second by omega, show ¬third < second by omega]
  | middle =>
      let edge := edgeFor snapshot upperNode treeDepth .middle
      have light : TernaryBranch.middle ≠ upperNode.heavyBranch snapshot := by
        rw [upperHeavy]
        decide
      have localMember : edge ∈ edgesAtNode snapshot upperNode treeDepth := by
        simp only [edgesAtNode, List.mem_map]
        exact ⟨.middle,
          (mem_lightBranches_iff snapshot upperNode .middle).2 light, rfl⟩
      have member : edge ∈ treeEdges snapshot before upper_le_n treeDepth := by
        simp only [before, treeEdges, List.mem_append]
        exact Or.inl (Or.inl localMember)
      refine ⟨edge, member, rfl, ?_⟩
      change first ∈ zigZigHitSupport before third 0
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      simp [zigZigHitSupport, before, _root_.Splay.Tree.BST.searchPath,
        show third ≠ first by omega, show ¬third < first by omega,
        show third ≠ second by omega, show ¬third < second by omega]
  | right =>
      let edge := edgeFor snapshot lowerNode (treeDepth + 1) .left
      have light : TernaryBranch.left ≠ lowerNode.heavyBranch snapshot := by
        rw [lowerHeavy]
        decide
      have localMember :
          edge ∈ edgesAtNode snapshot lowerNode (treeDepth + 1) := by
        simp only [edgesAtNode, List.mem_map]
        exact ⟨.left,
          (mem_lightBranches_iff snapshot lowerNode .left).2 light, rfl⟩
      have member : edge ∈ treeEdges snapshot before upper_le_n treeDepth := by
        have literalMember :
            edge ∈ edgesAtNode snapshot {
              lower := first + 1
              root := second
              upper := upper
              left := b
              right := .node c d
              upper_le_n := upper_le_n
            } (treeDepth + 1) := by
          simpa only [lowerNode] using localMember
        simp only [before, treeEdges, List.mem_append]
        aesop
      have childEq : edge.child = endpointNode.branchMin snapshot .right := by
        change lowerNode.branchMin snapshot .left =
          endpointNode.branchMin snapshot .right
        unfold AtNode.branchMin
        have lowerEq :
            lowerNode.branchLower .left =
              endpointNode.branchLower .right := by
          apply Fin.ext
          simp [AtNode.branchLower, AtNode.wholeLower, lowerNode,
            endpointNode]
          omega
        have upperEq :
            lowerNode.branchUpper .left =
              endpointNode.branchUpper .right := by
          apply Fin.ext
          simp [AtNode.branchUpper, AtNode.wholeUpper, lowerNode,
            endpointNode]
        cases lowerEq
        cases upperEq
        rfl
      refine ⟨edge, member, childEq, ?_⟩
      change second ∈ zigZigHitSupport before third 0
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      simp [zigZigHitSupport, before, _root_.Splay.Tree.BST.searchPath,
        show third ≠ first by omega, show ¬third < first by omega,
        show third ≠ second by omega, show ¬third < second by omega]

/--
Both heap-child endpoints of a concrete zig-zig pairing are incident, in the
pre-rotation tree, to one of that zig-zig's two persistent hit nodes.
-/
theorem heapChildren_supported
    {n : ℕ} {snapshot : Snapshot n} {phase : PairingPhase}
    {depth key lower upper : ℕ} {before after : BST lower upper}
    {winner loser : External n}
    (endpoints :
      ZigZigPairingEndpointsAt snapshot phase
        (depth := depth) (key := key) before after winner loser)
    (upper_le_n : upper ≤ n) (treeDepth : ℕ)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    HeapChildSupportedAt snapshot before upper_le_n treeDepth
        (zigZigHitSupport before key depth) winner ∧
      HeapChildSupportedAt snapshot before upper_le_n treeDepth
        (zigZigHitSupport before key depth) loser := by
  induction endpoints generalizing treeDepth with
  | @zigZigLeft lower first second third upper a b c d storedUpper phase =>
      let endpointNode : AtNode n := {
        lower := _ + 1
        root := _
        upper := _
        left := c
        right := d
        upper_le_n := storedUpper
      }
      have winnerSupported :=
        zigZigLeft_branch_supported snapshot a b c d storedUpper
          (by simpa [valuePos] using rankZero)
          (endpointNode.heavyBranch snapshot) treeDepth
      have loserSupported :=
        zigZigLeft_branch_supported snapshot a b c d storedUpper
          (by simpa [valuePos] using rankZero)
          (HeapChildPairing.loserBranch
            (endpointNode.heavyBranch snapshot) phase) treeDepth
      have winnerSupported' :
          HeapChildSupportedAt snapshot
            (.node (.node (.node a b) c) d) storedUpper treeDepth
            (zigZigHitSupport (.node (.node (.node a b) c) d) first 0)
            (endpointNode.branchMin snapshot
              (endpointNode.heavyBranch snapshot)) := by
        simpa only [endpointNode] using winnerSupported
      have winnerOwner :
          HeapChildSupportedAt snapshot
            (.node (.node (.node a b) c) d) storedUpper treeDepth
            (zigZigHitSupport (.node (.node (.node a b) c) d) first 0)
            (endpointNode.owner snapshot) := by
        rw [endpointNode.owner_eq_branchMin_heavy snapshot]
        exact winnerSupported'
      constructor
      · simpa [HeapChildPairing.ofNode, endpointNode] using winnerOwner
      · simpa [HeapChildPairing.ofNode, endpointNode] using loserSupported
  | @zigZigRight lower first second third upper a b c d storedUpper
      second_le_n phase =>
      let endpointNode : AtNode n := {
        lower := _
        root := _
        upper := _
        left := a
        right := b
        upper_le_n := second_le_n
      }
      have winnerSupported :=
        zigZigRight_branch_supported snapshot a b c d storedUpper
          (by simpa [valuePos] using rankZero)
          (endpointNode.heavyBranch snapshot) treeDepth
      have loserSupported :=
        zigZigRight_branch_supported snapshot a b c d storedUpper
          (by simpa [valuePos] using rankZero)
          (HeapChildPairing.loserBranch
            (endpointNode.heavyBranch snapshot) phase) treeDepth
      have winnerSupported' :
          HeapChildSupportedAt snapshot
            (.node a (.node b (.node c d))) storedUpper treeDepth
            (zigZigHitSupport (.node a (.node b (.node c d))) third 0)
            (endpointNode.branchMin snapshot
              (endpointNode.heavyBranch snapshot)) := by
        simpa only [endpointNode] using winnerSupported
      have winnerOwner :
          HeapChildSupportedAt snapshot
            (.node a (.node b (.node c d))) storedUpper treeDepth
            (zigZigHitSupport (.node a (.node b (.node c d))) third 0)
            (endpointNode.owner snapshot) := by
        rw [endpointNode.owner_eq_branchMin_heavy snapshot]
        exact winnerSupported'
      constructor
      · simpa [HeapChildPairing.ofNode, endpointNode] using winnerOwner
      · simpa [HeapChildPairing.ofNode, endpointNode] using loserSupported
  | @leftContext phase depth key lower root upper childBefore childAfter
      winner loser inside right ih =>
      have root_le_n : root ≤ n := by
        have := right.lower_le_upper
        omega
      have childKeyLt : key < root := inside.key_bounds.2
      have childResult :=
        ih root_le_n (treeDepth + 1) key_lt_n rankZero
      have supportEq :=
        zigZigHitSupport_leftContext (depth := depth)
          childBefore right childKeyLt
      constructor
      · simpa only [supportEq] using
          HeapChildSupportedAt.leftContext right childResult.1
      · simpa only [supportEq] using
          HeapChildSupportedAt.leftContext right childResult.2
  | @rightContext phase depth key lower root upper left childBefore
      childAfter winner loser inside ih =>
      have rootLtKey : root < key := by
        have := inside.key_bounds.1
        omega
      have childResult :=
        ih upper_le_n (treeDepth + 1) key_lt_n rankZero
      have supportEq :=
        zigZigHitSupport_rightContext (depth := depth)
          left childBefore rootLtKey
      constructor
      · simpa only [supportEq] using
          HeapChildSupportedAt.rightContext left childResult.1
      · simpa only [supportEq] using
          HeapChildSupportedAt.rightContext left childResult.2

end ZigZigPairingEndpointsAt

namespace SplayExecutionTranscript

/--
The actual phase-specific endpoint list obtained by following a concrete
splay transcript.  A zig-zig contributes its canonical winner and selected
phase loser; other splay steps contribute no pairing.
-/
inductive PhaseSelections {n : ℕ} (snapshot : Snapshot n)
    (phase : PairingPhase) (key : ℕ) :
    {lower upper : ℕ} → {before after : BST lower upper} →
      {execution : SplayExecution key before after} →
        {kinds : List SplayStepKind} → {zig zigZig zigZag : ℕ} →
          SplayExecutionTranscript key execution kinds zig zigZig zigZag →
            List (List (External n)) → Prop
  | done {lower upper : ℕ} {tree : BST lower upper}
      (root : tree.HasRoot key) :
      PhaseSelections snapshot phase key (.done root) []
  | zig {lower upper : ℕ} {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (step : Zig key before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {selections : List (List (External n))}
      (rest : PhaseSelections snapshot phase key tailTranscript selections) :
      PhaseSelections snapshot phase key
        (.zig step tail tailTranscript) selections
  | zigZig {depth lower upper : ℕ}
      {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (step : DoubleRotationAt depth key before middle)
      (orientation :
        DoubleOrientationAt true
          (depth := depth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {winner loser : External n}
      (endpoints :
        ZigZigPairingEndpointsAt snapshot phase
          (depth := depth) (key := key) before middle winner loser)
      {selections : List (List (External n))}
      (rest : PhaseSelections snapshot phase key tailTranscript selections) :
      PhaseSelections snapshot phase key
        (.zigZig step orientation tail tailTranscript)
        ([winner, loser] :: selections)
  | zigZag {depth lower upper : ℕ}
      {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (step : DoubleRotationAt depth key before middle)
      (orientation :
        DoubleOrientationAt false
          (depth := depth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {selections : List (List (External n))}
      (rest : PhaseSelections snapshot phase key tailTranscript selections) :
      PhaseSelections snapshot phase key
        (.zigZag step orientation tail tailTranscript) selections

/--
For either pairing phase, choose the genuine winner/loser endpoints of every
zig-zig and witness all of their incoming edges in the tree that existed
before the complete splay.
-/
theorem exists_phaseSelections_supported
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (phase : PairingPhase) :
    ∃ selections : List (List (External n)),
      PhaseSelections snapshot phase key transcript selections ∧
        List.Forall₂
          (HeapChildrenSupportedIn snapshot before upper_le_n)
          transcript.hitGroups selections := by
  induction transcript with
  | done root =>
      refine ⟨[], .done root, ?_⟩
      simp [hitGroups, zigZigHitGroups]
  | @zig lower upper before middle after kinds zig zigZig zigZag
      step tail tailTranscript ih =>
      have kindsNil :=
        tailTranscript.kinds_eq_nil_of_hasRoot_before step.hasRoot_after
      obtain ⟨tailSelections, tailPhase, tailAligned⟩ := ih upper_le_n
      subst kinds
      have tailGroupsEmpty : tailTranscript.hitGroups = [] := by
        simp [hitGroups, zigZigHitGroups]
      rw [tailGroupsEmpty] at tailAligned
      cases tailAligned
      refine ⟨[], .zig step tail tailTranscript tailPhase, ?_⟩
      simp [hitGroups, zigZigHitGroups]
  | @zigZig depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail tailTranscript ih =>
      obtain ⟨tailSelections, tailPhase, tailAligned⟩ :=
        ih upper_le_n
      have tailSupportedInAncestors :
          ∀ support ∈ tailTranscript.hitGroups,
            ∀ attachment ∈ support,
              attachment ∈ (middle.searchPath key).dropLast.reverse := by
        intro support supportMember attachment attachmentMember
        apply tailTranscript.flatten_hitGroups_sublist_hitNodes.mem
        simp only [hitGroups, SplayExecution.hitNodes]
        exact List.mem_flatten.mpr
          ⟨support, supportMember, attachmentMember⟩
      have tailAlignedBefore :=
        HeapChildrenSupportedIn.pullback_double step upper_le_n
          tailSupportedInAncestors tailAligned
      obtain ⟨winner, loser, endpoints⟩ :=
        ZigZigPairingEndpointsAt.exists_of_orientation
          snapshot orientation upper_le_n phase
      have localSupport :=
        endpoints.heapChildren_supported upper_le_n 0 key_lt_n rankZero
      have headSupported :
          HeapChildrenSupportedIn snapshot before upper_le_n
            ((before.searchPath key).dropLast.reverse |>.take 2)
            [winner, loser] := by
        refine ⟨by simp, ?_, ?_⟩
        · have winnerNe : winner ≠ loser := by
            intro equal
            have rankLt := endpoints.rank_lt
            rw [equal] at rankLt
            exact Nat.lt_irrefl _ rankLt
          simp [winnerNe]
        · intro child childMember
          simp at childMember
          rcases childMember with rfl | rfl
          · obtain ⟨edge, edgeMember, childEq, attachmentMember⟩ :=
              localSupport.1
            exact ⟨edge, edgeMember, childEq,
              (Splay.Accounting.DoubleRotationAt.mem_zigZigHitSupport_iff_mem_take_properAncestors
                  (node := edge.attachmentKey) step).mp attachmentMember⟩
          · obtain ⟨edge, edgeMember, childEq, attachmentMember⟩ :=
              localSupport.2
            exact ⟨edge, edgeMember, childEq,
              (Splay.Accounting.DoubleRotationAt.mem_zigZigHitSupport_iff_mem_take_properAncestors
                  (node := edge.attachmentKey) step).mp attachmentMember⟩
      refine ⟨[winner, loser] :: tailSelections,
        .zigZig step orientation tail tailTranscript endpoints tailPhase, ?_⟩
      apply List.Forall₂.cons headSupported
      simpa only [hitGroups, SplayExecution.hitNodes, zigZigHitGroups,
        SplayExecution.drop_two_hitNodes_of_double step] using tailAlignedBefore
  | @zigZag depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail tailTranscript ih =>
      obtain ⟨tailSelections, tailPhase, tailAligned⟩ :=
        ih upper_le_n
      have tailSupportedInAncestors :
          ∀ support ∈ tailTranscript.hitGroups,
            ∀ attachment ∈ support,
              attachment ∈ (middle.searchPath key).dropLast.reverse := by
        intro support supportMember attachment attachmentMember
        apply tailTranscript.flatten_hitGroups_sublist_hitNodes.mem
        simp only [hitGroups, SplayExecution.hitNodes]
        exact List.mem_flatten.mpr
          ⟨support, supportMember, attachmentMember⟩
      have tailAlignedBefore :=
        HeapChildrenSupportedIn.pullback_double step upper_le_n
          tailSupportedInAncestors tailAligned
      refine ⟨tailSelections,
        .zigZag step orientation tail tailTranscript tailPhase, ?_⟩
      simpa only [hitGroups, SplayExecution.hitNodes,
        zigZigHitGroups,
        SplayExecution.drop_two_hitNodes_of_double step] using
          tailAlignedBefore

/--
Manuscript Lemma `pairings-in-parallel`: for one complete splay, the genuine
first-pairing endpoints are jointly duplicate-free, and so are the genuine
second-pairing endpoints.  Each phase contains exactly one two-endpoint
selection per zig-zig.
-/
theorem pairings_in_parallel
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    ∃ firstSelections secondSelections : List (List (External n)),
      PhaseSelections snapshot .first key transcript firstSelections ∧
        PhaseSelections snapshot .second key transcript secondSelections ∧
        firstSelections.length = zigZig ∧
        secondSelections.length = zigZig ∧
        firstSelections.flatten.Nodup ∧
        secondSelections.flatten.Nodup := by
  obtain ⟨firstSelections, firstActual, firstSupported⟩ :=
    transcript.exists_phaseSelections_supported upper_le_n key_lt_n
      rankZero .first
  obtain ⟨secondSelections, secondActual, secondSupported⟩ :=
    transcript.exists_phaseSelections_supported upper_le_n key_lt_n
      rankZero .second
  have firstLength : firstSelections.length = zigZig := by
    rw [← transcript.length_hitGroups]
    exact firstSupported.length_eq.symm
  have secondLength : secondSelections.length = zigZig := by
    rw [← transcript.length_hitGroups]
    exact secondSupported.length_eq.symm
  have firstNodup : firstSelections.flatten.Nodup :=
    HeapChildrenSupportedIn.flatten_nodup
      transcript.flatten_zigZigHitGroups_nodup firstSupported
  have secondNodup : secondSelections.flatten.Nodup :=
    HeapChildrenSupportedIn.flatten_nodup
      transcript.flatten_zigZigHitGroups_nodup secondSupported
  exact ⟨firstSelections, secondSelections, firstActual, secondActual,
    firstLength, secondLength, firstNodup, secondNodup⟩

end SplayExecutionTranscript

end Splay.Accounting
