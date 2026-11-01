import Splay.Accounting.WholeSplayTemporaryPriorityReduction

namespace Splay.Accounting.WholeSplayRestorationGeometry

open Splay.Rank
open Splay.Tree
open Splay.Lazy.Canonical
open Splay.Accounting.JunctionBendReduction
open Splay.Accounting.WholeSplayTemporaryPriorityReduction

/--
A local description of a one-boundary rank restoration.

Every junction must lie on the fixed splay-tree search path to `special`;
moreover, the branch towards `special` is light in the restored snapshot.
This is much weaker than supplying the resulting heap-ancestor chain by
hand.  The recursion below constructs that chain automatically.
-/
structure LocalizedJunctionGeometry
    {n : ℕ} (before after restored : Snapshot n)
    (special : External n) : Prop where
  junction_special :
    ∀ node : AtNode n,
      before.IsJunction after
          node.wholeLower node.wholeUpper node.whole_nonempty node.root →
        (node.wholeLower ≤ special ∧ special ≤ node.wholeUpper) ∧
          ∀ branch,
            branch.Contains node.root special.val →
              branch ≠ node.heavyBranch restored

namespace LocalizedJunctionGeometry

private theorem heavyBranch_eq_of_intervalMin_eq
    {n : ℕ} {first second : Snapshot n}
    {lower upper : External n} {nonempty : lower ≤ upper}
    {root : ℕ}
    (minimumEq :
      first.intervalMin lower upper nonempty =
        second.intervalMin lower upper nonempty) :
    first.heavyBranch lower upper nonempty root =
      second.heavyBranch lower upper nonempty root := by
  by_contra junction
  exact
    (Snapshot.IsJunction.intervalMin_ne
      (before := first) (after := second) junction) minimumEq

/--
Interval-minimum localization is sufficient for the local junction
geometry.  This is the small interface used by both canonical restoration
phases below.
-/
theorem ofIntervalMinGeometry
    {n : ℕ} {before after restored : Snapshot n}
    {special : External n}
    (beforeMinimum :
      ∀ lower upper (nonempty : lower ≤ upper),
        before.intervalMin lower upper nonempty ≠
            after.intervalMin lower upper nonempty →
          before.intervalMin lower upper nonempty = special)
    (afterMinimum :
      ∀ lower upper (nonempty : lower ≤ upper),
        before.intervalMin lower upper nonempty ≠
            after.intervalMin lower upper nonempty →
          after.intervalMin lower upper nonempty =
            restored.intervalMin lower upper nonempty) :
    LocalizedJunctionGeometry before after restored special where
  junction_special node junction := by
    have minimumNe :=
      Snapshot.IsJunction.intervalMin_ne junction
    have beforeEq :=
      beforeMinimum node.wholeLower node.wholeUpper
        node.whole_nonempty minimumNe
    have afterEq :=
      afterMinimum node.wholeLower node.wholeUpper
        node.whole_nonempty minimumNe
    have minimumBefore :=
      before.intervalMin_isMin
        node.wholeLower node.wholeUpper node.whole_nonempty
    have specialInside :
        node.wholeLower ≤ special ∧ special ≤ node.wholeUpper := by
      rw [beforeEq] at minimumBefore
      exact ⟨minimumBefore.1, minimumBefore.2.1⟩
    refine ⟨specialInside, ?_⟩
    intro branch branchContains branchIsRestored
    have beforeContains :=
      before.heavyBranch_contains_intervalMin
        node.wholeLower node.wholeUpper node.whole_nonempty node.root
    rw [beforeEq] at beforeContains
    obtain ⟨selected, _, selectedUnique⟩ :=
      TernaryBranch.existsUnique_contains node.root special.val
    have beforeBranchEq :
        node.heavyBranch before = branch :=
      (selectedUnique _ beforeContains).trans
        (selectedUnique _ branchContains).symm
    have afterRestoredEq :
        node.heavyBranch after = node.heavyBranch restored :=
      heavyBranch_eq_of_intervalMin_eq afterEq
    exact junction
      (beforeBranchEq.trans
        (branchIsRestored.trans afterRestoredEq.symm))

private structure PathCertificate
    {n lower upper : ℕ} (before after restored : Snapshot n)
    (special : External n) (tree : BST lower upper)
    (upper_le_n : upper ≤ n) : Type where
  ancestors : List (External n)
  chain :
    IsHeapAncestorChain restored.rank (special :: ancestors)
  junctions_le_length :
    junctionCountFrom before after tree upper_le_n ≤
      (special :: ancestors).length
  inside :
    ∀ element ∈ special :: ancestors,
      subtreeLower tree upper_le_n ≤ element ∧
        element ≤ subtreeUpper tree upper_le_n

private theorem junctionCountFrom_eq_zero_of_outside
    {n lower upper : ℕ} {before after restored : Snapshot n}
    {special : External n}
    (geometry :
      LocalizedJunctionGeometry before after restored special)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (outside :
      special < subtreeLower tree upper_le_n ∨
        subtreeUpper tree upper_le_n < special) :
    junctionCountFrom before after tree upper_le_n = 0 := by
  induction tree with
  | empty boundary =>
      simp [junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have left_le_n : root ≤ n := by
        have bounds := right.lower_le_upper
        omega
      have rootNotJunction :
          node.heavyBranch before = node.heavyBranch after := by
        by_contra junction
        have localized :=
          geometry.junction_special node (by
            exact junction)
        rcases outside with outside | outside
        · exact (not_le_of_gt outside) localized.1.1
        · exact (not_le_of_gt outside) localized.1.2
      have leftOutside :
          special < subtreeLower left left_le_n ∨
            subtreeUpper left left_le_n < special := by
        rcases outside with outside | outside
        · exact Or.inl (by
            change special.val < 2 * lower
            change special.val < 2 * lower at outside
            exact outside)
        · exact Or.inr (by
            change 2 * root < special.val
            change 2 * upper < special.val at outside
            have bounds := right.lower_le_upper
            omega)
      have rightOutside :
          special < subtreeLower right upper_le_n ∨
            subtreeUpper right upper_le_n < special := by
        rcases outside with outside | outside
        · exact Or.inl (by
            change special.val < 2 * (root + 1)
            change special.val < 2 * lower at outside
            have bounds := left.lower_le_upper
            omega)
        · exact Or.inr (by
            change 2 * upper < special.val
            change 2 * upper < special.val at outside
            exact outside)
      have leftZero := ihLeft left_le_n leftOutside
      have rightZero := ihRight upper_le_n rightOutside
      simp only [junctionCountFrom]
      change
        (if node.heavyBranch before = node.heavyBranch after
          then 0 else 1) +
            junctionCountFrom before after left left_le_n +
            junctionCountFrom before after right upper_le_n = 0
      simp [rootNotJunction, leftZero, rightZero]

private noncomputable def pathCertificate
    {n lower upper : ℕ} {before after restored : Snapshot n}
    {special : External n}
    (geometry :
      LocalizedJunctionGeometry before after restored special)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (specialInside :
      subtreeLower tree upper_le_n ≤ special ∧
        special ≤ subtreeUpper tree upper_le_n) :
    PathCertificate before after restored special tree upper_le_n := by
  induction tree with
  | empty boundary =>
      refine {
        ancestors := []
        chain := by simp [IsHeapAncestorChain]
        junctions_le_length := by simp [junctionCountFrom]
        inside := ?_
      }
      intro element member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst element
      exact specialInside
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have left_le_n : root ≤ n := by
        have bounds := right.lower_le_upper
        omega
      by_cases inLeft : special.val ≤ 2 * root
      · have specialInsideLeft :
            subtreeLower left left_le_n ≤ special ∧
              special ≤ subtreeUpper left left_le_n := by
          constructor
          · change 2 * lower ≤ special.val
            have lowerInside := specialInside.1
            change 2 * lower ≤ special.val at lowerInside
            exact lowerInside
          · exact inLeft
        have rightOutside :
            special < subtreeLower right upper_le_n ∨
              subtreeUpper right upper_le_n < special :=
          Or.inl (by
            change special.val < 2 * (root + 1)
            omega)
        let child :=
          ihLeft left_le_n specialInsideLeft
        have rightZero :=
          junctionCountFrom_eq_zero_of_outside
            geometry right upper_le_n rightOutside
        by_cases rootSame :
            node.heavyBranch before = node.heavyBranch after
        · refine {
            ancestors := child.ancestors
            chain := child.chain
            junctions_le_length := ?_
            inside := ?_
          }
          · simp only [junctionCountFrom]
            change
              (if node.heavyBranch before = node.heavyBranch after
                then 0 else 1) +
                  junctionCountFrom before after left left_le_n +
                  junctionCountFrom before after right upper_le_n ≤
                    (special :: child.ancestors).length
            simpa [rootSame, rightZero] using child.junctions_le_length
          · intro element member
            have childInside := child.inside element member
            constructor
            · change 2 * lower ≤ element.val
              have lowerInside := childInside.1
              change 2 * lower ≤ element.val at lowerInside
              exact lowerInside
            · change element.val ≤ 2 * upper
              have upperInside := childInside.2
              change element.val ≤ 2 * root at upperInside
              have bounds := right.lower_le_upper
              omega
        · have localized :=
            geometry.junction_special node (by exact rootSame)
          have branchLight :
              TernaryBranch.left ≠ node.heavyBranch restored :=
            localized.2 .left inLeft
          have ownerLtBranch :=
            node.owner_rank_lt_branchMin_of_light restored branchLight
          refine {
            ancestors := child.ancestors ++ [node.owner restored]
            chain := ?_
            junctions_le_length := ?_
            inside := ?_
          }
          · change
              IsHeapAncestorChain restored.rank
                ((special :: child.ancestors) ++ [node.owner restored])
            apply child.chain.append (.singleton _)
            intro last lastMember owner ownerMember
            simp only [List.head?_singleton, Option.mem_some_iff] at ownerMember
            subst owner
            have lastInside :=
              child.inside last (List.mem_of_mem_getLast? lastMember)
            have branchLeLast :=
              (node.branchMin_isMin restored .left).2.2
                last lastInside.1 lastInside.2
            exact ownerLtBranch.trans_le branchLeLast
          · simp only [junctionCountFrom]
            change
              (if node.heavyBranch before = node.heavyBranch after
                then 0 else 1) +
                  junctionCountFrom before after left left_le_n +
                  junctionCountFrom before after right upper_le_n ≤
                    (special ::
                      (child.ancestors ++ [node.owner restored])).length
            simp [rootSame, rightZero]
            have bound :=
              Nat.add_le_add_right child.junctions_le_length 1
            simpa only [List.length_cons, List.length_append,
              List.length_singleton, Nat.add_comm] using bound
          · intro element member
            by_cases isOwner : element = node.owner restored
            · subst element
              exact
                ⟨(node.owner_isMin restored).1,
                  (node.owner_isMin restored).2.1⟩
            · have childMember :
                  element ∈ special :: child.ancestors := by
                simpa [isOwner] using member
              have childInside :=
                child.inside element childMember
              constructor
              · change 2 * lower ≤ element.val
                have lowerInside := childInside.1
                change 2 * lower ≤ element.val at lowerInside
                exact lowerInside
              · change element.val ≤ 2 * upper
                have upperInside := childInside.2
                change element.val ≤ 2 * root at upperInside
                have bounds := right.lower_le_upper
                omega
      · by_cases inMiddle : special.val = 2 * root + 1
        · have leftOutside :
              special < subtreeLower left left_le_n ∨
                subtreeUpper left left_le_n < special :=
            Or.inr (by
              change 2 * root < special.val
              omega)
          have rightOutside :
              special < subtreeLower right upper_le_n ∨
                subtreeUpper right upper_le_n < special :=
            Or.inl (by
              change special.val < 2 * (root + 1)
              omega)
          have leftZero :=
            junctionCountFrom_eq_zero_of_outside
              geometry left left_le_n leftOutside
          have rightZero :=
            junctionCountFrom_eq_zero_of_outside
              geometry right upper_le_n rightOutside
          by_cases rootSame :
              node.heavyBranch before = node.heavyBranch after
          · refine {
              ancestors := []
              chain := by simp [IsHeapAncestorChain]
              junctions_le_length := ?_
              inside := ?_
            }
            · simp only [junctionCountFrom]
              change
                (if node.heavyBranch before = node.heavyBranch after
                  then 0 else 1) +
                    junctionCountFrom before after left left_le_n +
                    junctionCountFrom before after right upper_le_n ≤ 1
              simp [rootSame, leftZero, rightZero]
            · intro element member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              subst element
              exact specialInside
          · have localized :=
              geometry.junction_special node (by exact rootSame)
            have branchLight :
                TernaryBranch.middle ≠ node.heavyBranch restored :=
              localized.2 .middle inMiddle
            have ownerLtBranch :=
              node.owner_rank_lt_branchMin_of_light restored branchLight
            have branchMinEq :
                node.branchMin restored .middle = special := by
              apply Fin.ext
              have minimum := node.branchMin_isMin restored .middle
              change (node.branchMin restored .middle).val =
                special.val
              have minimumLower := minimum.1
              have minimumUpper := minimum.2.1
              change 2 * root + 1 ≤
                (node.branchMin restored .middle).val at minimumLower
              change
                (node.branchMin restored .middle).val ≤
                  2 * root + 1 at minimumUpper
              omega
            have ownerLtSpecial :
                restored.rank (node.owner restored) <
                  restored.rank special := by
              simpa [branchMinEq] using ownerLtBranch
            refine {
              ancestors := [node.owner restored]
              chain := by
                simp [IsHeapAncestorChain, ownerLtSpecial]
              junctions_le_length := ?_
              inside := ?_
            }
            · simp only [junctionCountFrom]
              change
                (if node.heavyBranch before = node.heavyBranch after
                  then 0 else 1) +
                    junctionCountFrom before after left left_le_n +
                    junctionCountFrom before after right upper_le_n ≤ 2
              simp [rootSame, leftZero, rightZero]
            · intro element member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | member
              · exact specialInside
              · rcases member with rfl
                exact
                  ⟨(node.owner_isMin restored).1,
                    (node.owner_isMin restored).2.1⟩
        · have inRight : 2 * root + 2 ≤ special.val := by
            omega
          have specialInsideRight :
              subtreeLower right upper_le_n ≤ special ∧
                special ≤ subtreeUpper right upper_le_n := by
            exact ⟨inRight, specialInside.2⟩
          have leftOutside :
              special < subtreeLower left left_le_n ∨
                subtreeUpper left left_le_n < special :=
            Or.inr (by
              change 2 * root < special.val
              omega)
          let child :=
            ihRight upper_le_n specialInsideRight
          have leftZero :=
            junctionCountFrom_eq_zero_of_outside
              geometry left left_le_n leftOutside
          by_cases rootSame :
              node.heavyBranch before = node.heavyBranch after
          · refine {
              ancestors := child.ancestors
              chain := child.chain
              junctions_le_length := ?_
              inside := ?_
            }
            · simp only [junctionCountFrom]
              change
                (if node.heavyBranch before = node.heavyBranch after
                  then 0 else 1) +
                    junctionCountFrom before after left left_le_n +
                    junctionCountFrom before after right upper_le_n ≤
                      (special :: child.ancestors).length
              simpa [rootSame, leftZero] using child.junctions_le_length
            · intro element member
              have childInside := child.inside element member
              constructor
              · change 2 * lower ≤ element.val
                have lowerInside := childInside.1
                change 2 * (root + 1) ≤ element.val at lowerInside
                have bounds := left.lower_le_upper
                omega
              · exact childInside.2
          · have localized :=
              geometry.junction_special node (by exact rootSame)
            have branchLight :
                TernaryBranch.right ≠ node.heavyBranch restored :=
              localized.2 .right inRight
            have ownerLtBranch :=
              node.owner_rank_lt_branchMin_of_light restored branchLight
            refine {
              ancestors := child.ancestors ++ [node.owner restored]
              chain := ?_
              junctions_le_length := ?_
              inside := ?_
            }
            · change
                IsHeapAncestorChain restored.rank
                  ((special :: child.ancestors) ++ [node.owner restored])
              apply child.chain.append (.singleton _)
              intro last lastMember owner ownerMember
              simp only [List.head?_singleton, Option.mem_some_iff] at ownerMember
              subst owner
              have lastInside :=
                child.inside last (List.mem_of_mem_getLast? lastMember)
              have branchLeLast :=
                (node.branchMin_isMin restored .right).2.2
                  last lastInside.1 lastInside.2
              exact ownerLtBranch.trans_le branchLeLast
            · simp only [junctionCountFrom]
              change
                (if node.heavyBranch before = node.heavyBranch after
                  then 0 else 1) +
                    junctionCountFrom before after left left_le_n +
                    junctionCountFrom before after right upper_le_n ≤
                      (special ::
                        (child.ancestors ++ [node.owner restored])).length
              simp [rootSame, leftZero]
              have bound :=
                Nat.add_le_add_right child.junctions_le_length 1
              simpa only [List.length_cons, List.length_append,
                List.length_singleton, Nat.add_comm] using bound
            · intro element member
              by_cases isOwner : element = node.owner restored
              · subst element
                exact
                  ⟨(node.owner_isMin restored).1,
                    (node.owner_isMin restored).2.1⟩
              · have childMember :
                    element ∈ special :: child.ancestors := by
                  simpa [isOwner] using member
                have childInside :=
                  child.inside element childMember
                constructor
                · change 2 * lower ≤ element.val
                  have lowerInside := childInside.1
                  change 2 * (root + 1) ≤ element.val at lowerInside
                  have bounds := left.lower_le_upper
                  omega
                · exact childInside.2

/--
Local junction localization automatically produces the proof-relevant
heap-ancestor chain required by the whole-splay restoration accounting.
-/
noncomputable def toJunctionChainCertificate
    {n : ℕ} {before after restored : Snapshot n}
    {special : External n}
    (geometry :
      LocalizedJunctionGeometry before after restored special)
    (tree : BST 0 n) :
    JunctionChainCertificate restored.rank special
      (junctionCount before after tree) := by
  let path :=
    pathCertificate geometry tree (Nat.le_refl n) (by
      constructor
      · simp [subtreeLower]
      · change special.val ≤ 2 * n
        have bound := special.isLt
        omega)
  exact {
    ancestors := path.ancestors
    chain := path.chain
    junctions_le_length := path.junctions_le_length
  }

/--
The resulting junction count is bounded directly by the restored rank of the
selected boundary, with no manually supplied injection or ancestor list.
-/
theorem junctionCount_le_rank_succ
    {n : ℕ} {before after restored : Snapshot n}
    {special : External n}
    (geometry :
      LocalizedJunctionGeometry before after restored special)
    (tree : BST 0 n) :
    junctionCount before after tree ≤ restored.rank special + 1 :=
  (geometry.toJunctionChainCertificate tree).junctions_le_rank_succ

end LocalizedJunctionGeometry

private theorem rank_pos_of_ne_zero
    {n : ℕ} (snapshot : Snapshot n)
    {root special : External n}
    (rootRank : snapshot.rank root = 0)
    (different : special ≠ root) :
    0 < snapshot.rank special := by
  by_contra notPositive
  have specialRank : snapshot.rank special = 0 := by omega
  let lower : External n := ⟨0, by omega⟩
  let upper : External n := ⟨2 * n, by omega⟩
  have nonempty : lower ≤ upper := by
    simp [lower, upper]
  have rootMinimum :
      IsIntervalMin snapshot.rank lower upper root := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 ≤ root.val
      omega
    · change root.val ≤ 2 * n
      omega
    · intro element _ _
      rw [rootRank]
      omega
  have specialMinimum :
      IsIntervalMin snapshot.rank lower upper special := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 ≤ special.val
      omega
    · change special.val ≤ 2 * n
      omega
    · intro element _ _
      rw [specialRank]
      omega
  have rootEq :=
    snapshot.intervalMin_unique lower upper nonempty rootMinimum
  have specialEq :=
    snapshot.intervalMin_unique lower upper nonempty specialMinimum
  exact different (specialEq.trans rootEq.symm)

private theorem oneBoundary_intervalMin_eq_of_outside
    {n : ℕ} (snapshot : Snapshot n)
    (root special : External n)
    (different : special ≠ root)
    (rootRank : snapshot.rank root = 0)
    (lower upper : External n) (nonempty : lower ≤ upper)
    (outside : special < lower ∨ upper < special) :
    (snapshot.withOneBoundaryTemporaryPriority
        root special different rootRank).intervalMin
          lower upper nonempty =
      snapshot.intervalMin lower upper nonempty := by
  let temporary :=
    snapshot.withOneBoundaryTemporaryPriority
      root special different rootRank
  let candidate :=
    snapshot.intervalMin lower upper nonempty
  have candidateMinimum :=
    snapshot.intervalMin_isMin lower upper nonempty
  have candidateOrdinary : candidate ≠ special := by
    intro equal
    have specialLower : lower ≤ special := by
      exact
        Eq.mp (congrArg (fun element => lower ≤ element) equal)
          candidateMinimum.1
    have specialUpper : special ≤ upper := by
      exact
        Eq.mp (congrArg (fun element => element ≤ upper) equal)
          candidateMinimum.2.1
    rcases outside with outside | outside
    · exact (not_le_of_gt outside) specialLower
    · exact (not_le_of_gt outside) specialUpper
  have temporaryMinimum :
      IsIntervalMin temporary.rank lower upper candidate := by
    refine ⟨candidateMinimum.1, candidateMinimum.2.1, ?_⟩
    intro element elementLower elementUpper
    have elementOrdinary : element ≠ special := by
      intro equal
      subst element
      rcases outside with outside | outside
      · exact (not_le_of_gt outside) elementLower
      · exact (not_le_of_gt outside) elementUpper
    change
      oneBoundaryTemporaryRank snapshot special candidate ≤
        oneBoundaryTemporaryRank snapshot special element
    rw [oneBoundaryTemporaryRank_eq_truePriority
        snapshot special candidate candidateOrdinary,
      oneBoundaryTemporaryRank_eq_truePriority
        snapshot special element elementOrdinary]
    exact Nat.mul_le_mul_left 2
      (candidateMinimum.2.2 element elementLower elementUpper)
  have candidateEq :=
    temporary.intervalMin_unique lower upper nonempty temporaryMinimum
  exact candidateEq.symm

private theorem oneBoundary_beforeMinimum_eq_special_of_ne
    {n : ℕ} (snapshot : Snapshot n)
    (root special : External n)
    (different : special ≠ root)
    (rootRank : snapshot.rank root = 0)
    (lower upper : External n) (nonempty : lower ≤ upper)
    (minimumNe :
      (snapshot.withOneBoundaryTemporaryPriority
          root special different rootRank).intervalMin
            lower upper nonempty ≠
        snapshot.intervalMin lower upper nonempty) :
    (snapshot.withOneBoundaryTemporaryPriority
        root special different rootRank).intervalMin
          lower upper nonempty = special := by
  let temporary :=
    snapshot.withOneBoundaryTemporaryPriority
      root special different rootRank
  let candidate :=
    temporary.intervalMin lower upper nonempty
  have candidateMinimum :=
    temporary.intervalMin_isMin lower upper nonempty
  by_contra candidateOrdinary
  have genuineMinimum :
      IsIntervalMin snapshot.rank lower upper candidate := by
    refine ⟨candidateMinimum.1, candidateMinimum.2.1, ?_⟩
    intro element elementLower elementUpper
    have temporaryLe :=
      candidateMinimum.2.2 element elementLower elementUpper
    by_cases elementSpecial : element = special
    · subst element
      change
        oneBoundaryTemporaryRank snapshot special candidate ≤
          oneBoundaryTemporaryRank snapshot special special at temporaryLe
      rw [oneBoundaryTemporaryRank_eq_truePriority
          snapshot special candidate candidateOrdinary,
        oneBoundaryTemporaryRank_eq_one] at temporaryLe
      simp only [truePriority] at temporaryLe
      omega
    · change
        oneBoundaryTemporaryRank snapshot special candidate ≤
          oneBoundaryTemporaryRank snapshot special element at temporaryLe
      rw [oneBoundaryTemporaryRank_eq_truePriority
          snapshot special candidate candidateOrdinary,
        oneBoundaryTemporaryRank_eq_truePriority
          snapshot special element elementSpecial] at temporaryLe
      simp only [truePriority] at temporaryLe
      omega
  have candidateEq :=
    snapshot.intervalMin_unique lower upper nonempty genuineMinimum
  exact minimumNe candidateEq

/--
Restoring one artificial boundary directly to the genuine snapshot has
localized junction geometry with respect to genuine ranks.
-/
theorem oneBoundaryLocalizedJunctionGeometry
    {n : ℕ} (snapshot : Snapshot n)
    (root special : External n)
    (different : special ≠ root)
    (rootRank : snapshot.rank root = 0) :
    LocalizedJunctionGeometry
      (snapshot.withOneBoundaryTemporaryPriority
        root special different rootRank)
      snapshot snapshot special :=
  LocalizedJunctionGeometry.ofIntervalMinGeometry
    (fun lower upper nonempty minimumNe =>
      oneBoundary_beforeMinimum_eq_special_of_ne
        snapshot root special different rootRank
          lower upper nonempty minimumNe)
    (fun _ _ _ _ => rfl)

/--
Hence the chain certificate for a canonical one-boundary-to-true restoration
is completely automatic.
-/
noncomputable def oneBoundaryJunctionChainCertificate
    {n : ℕ} (snapshot : Snapshot n)
    (root special : External n)
    (different : special ≠ root)
    (rootRank : snapshot.rank root = 0)
    (tree : BST 0 n) :
    JunctionChainCertificate snapshot.rank special
      (junctionCount
        (snapshot.withOneBoundaryTemporaryPriority
          root special different rootRank)
        snapshot tree) :=
  (oneBoundaryLocalizedJunctionGeometry
    snapshot root special different rootRank).toJunctionChainCertificate tree

private theorem twoToOne_beforeMinimum_eq_left_of_ne
    {n : ℕ} (snapshot : Snapshot n)
    (left root right : External n)
    (ordered : left < root ∧ root < right)
    (rootRank : snapshot.rank root = 0)
    (lower upper : External n) (nonempty : lower ≤ upper)
    (minimumNe :
      (snapshot.withTwoBoundaryTemporaryPriority
          left root right ordered rootRank).intervalMin
            lower upper nonempty ≠
        (snapshot.withOneBoundaryTemporaryPriority
          root right (ne_of_gt ordered.2) rootRank).intervalMin
              lower upper nonempty) :
    (snapshot.withTwoBoundaryTemporaryPriority
        left root right ordered rootRank).intervalMin
          lower upper nonempty = left := by
  have leftNeRoot : left ≠ root := ne_of_lt ordered.1
  have rightNeRoot : right ≠ root := ne_of_gt ordered.2
  have leftNeRight : left ≠ right :=
    ne_of_lt (ordered.1.trans ordered.2)
  let before :=
    snapshot.withTwoBoundaryTemporaryPriority
      left root right ordered rootRank
  let after :=
    snapshot.withOneBoundaryTemporaryPriority
      root right rightNeRoot rootRank
  have leftRankPositive :=
    rank_pos_of_ne_zero snapshot rootRank leftNeRoot
  have leftRankLe :
      before.rank left ≤ after.rank left := by
    change
      twoBoundaryTemporaryRank snapshot left right left ≤
        oneBoundaryTemporaryRank snapshot right left
    rw [twoBoundaryTemporaryRank_eq_one_left,
      oneBoundaryTemporaryRank_eq_truePriority
        snapshot right left leftNeRight]
    simp only [truePriority]
    omega
  have sameOffLeft :
      ∀ element : External n, element ≠ left →
        before.rank element = after.rank element := by
    intro element elementNeLeft
    by_cases elementRight : element = right
    · subst element
      change
        twoBoundaryTemporaryRank snapshot left right right =
          oneBoundaryTemporaryRank snapshot right right
      rw [twoBoundaryTemporaryRank_eq_one_right,
        oneBoundaryTemporaryRank_eq_one]
    · change
        twoBoundaryTemporaryRank snapshot left right element =
          oneBoundaryTemporaryRank snapshot right element
      rw [twoBoundaryTemporaryRank_eq_truePriority
          snapshot left right element ⟨elementNeLeft, elementRight⟩,
        oneBoundaryTemporaryRank_eq_truePriority
          snapshot right element elementRight]
  let candidate :=
    before.intervalMin lower upper nonempty
  have candidateMinimum :=
    before.intervalMin_isMin lower upper nonempty
  by_contra candidateNeLeft
  have afterMinimum :
      IsIntervalMin after.rank lower upper candidate := by
    refine ⟨candidateMinimum.1, candidateMinimum.2.1, ?_⟩
    intro element elementLower elementUpper
    have beforeLe :=
      candidateMinimum.2.2 element elementLower elementUpper
    rw [← sameOffLeft candidate candidateNeLeft]
    by_cases elementLeft : element = left
    · subst element
      exact beforeLe.trans leftRankLe
    · rw [← sameOffLeft element elementLeft]
      exact beforeLe
  have candidateEq :=
    after.intervalMin_unique lower upper nonempty afterMinimum
  exact minimumNe candidateEq

private theorem twoToOne_afterMinimum_eq_true_of_ne
    {n : ℕ} (snapshot : Snapshot n)
    (left root right : External n)
    (ordered : left < root ∧ root < right)
    (rootRank : snapshot.rank root = 0)
    (lower upper : External n) (nonempty : lower ≤ upper)
    (minimumNe :
      (snapshot.withTwoBoundaryTemporaryPriority
          left root right ordered rootRank).intervalMin
            lower upper nonempty ≠
        (snapshot.withOneBoundaryTemporaryPriority
          root right (ne_of_gt ordered.2) rootRank).intervalMin
              lower upper nonempty) :
    (snapshot.withOneBoundaryTemporaryPriority
        root right (ne_of_gt ordered.2) rootRank).intervalMin
            lower upper nonempty =
      snapshot.intervalMin lower upper nonempty := by
  have rightNeRoot : right ≠ root := ne_of_gt ordered.2
  have rootNeLeft : root ≠ left := ne_of_gt ordered.1
  have rootNeRight : root ≠ right := rightNeRoot.symm
  let before :=
    snapshot.withTwoBoundaryTemporaryPriority
      left root right ordered rootRank
  have beforeEq :=
    twoToOne_beforeMinimum_eq_left_of_ne
      snapshot left root right ordered rootRank
        lower upper nonempty minimumNe
  have beforeMinimum :=
    before.intervalMin_isMin lower upper nonempty
  have leftInside :
      lower ≤ left ∧ left ≤ upper := by
    rw [beforeEq] at beforeMinimum
    exact ⟨beforeMinimum.1, beforeMinimum.2.1⟩
  have rootOutside : ¬(lower ≤ root ∧ root ≤ upper) := by
    intro rootInside
    have leftLeRoot :=
      beforeMinimum.2.2 root rootInside.1 rootInside.2
    change
      twoBoundaryTemporaryRank snapshot left right
          (before.intervalMin lower upper nonempty) ≤
        twoBoundaryTemporaryRank snapshot left right root at leftLeRoot
    rw [beforeEq, twoBoundaryTemporaryRank_eq_one_left,
      twoBoundaryTemporaryRank_eq_truePriority
        snapshot left right root ⟨rootNeLeft, rootNeRight⟩,
      rootRank] at leftLeRoot
    simp [truePriority] at leftLeRoot
  have upperLtRoot : upper < root := by
    by_contra notLess
    apply rootOutside
    exact
      ⟨leftInside.1.trans (Nat.le_of_lt ordered.1),
        le_of_not_gt notLess⟩
  have rightOutside : upper < right :=
    upperLtRoot.trans ordered.2
  exact
    oneBoundary_intervalMin_eq_of_outside
      snapshot root right rightNeRoot rootRank lower upper nonempty
        (Or.inr rightOutside)

/--
The first canonical restoration, from two artificial boundaries to the
right-boundary-only snapshot, is localized with respect to the genuine
comparison ranks.
-/
theorem twoToOneLocalizedJunctionGeometry
    {n : ℕ} (snapshot : Snapshot n)
    (left root right : External n)
    (ordered : left < root ∧ root < right)
    (rootRank : snapshot.rank root = 0) :
    LocalizedJunctionGeometry
      (snapshot.withTwoBoundaryTemporaryPriority
        left root right ordered rootRank)
      (snapshot.withOneBoundaryTemporaryPriority
        root right (ne_of_gt ordered.2) rootRank)
      snapshot left :=
  LocalizedJunctionGeometry.ofIntervalMinGeometry
    (fun lower upper nonempty minimumNe =>
      twoToOne_beforeMinimum_eq_left_of_ne
        snapshot left root right ordered rootRank
          lower upper nonempty minimumNe)
    (fun lower upper nonempty minimumNe =>
      twoToOne_afterMinimum_eq_true_of_ne
        snapshot left root right ordered rootRank
          lower upper nonempty minimumNe)

/-- Automatic true-rank chain for the first canonical restoration phase. -/
noncomputable def twoToOneJunctionChainCertificate
    {n : ℕ} (snapshot : Snapshot n)
    (left root right : External n)
    (ordered : left < root ∧ root < right)
    (rootRank : snapshot.rank root = 0)
    (tree : BST 0 n) :
    JunctionChainCertificate snapshot.rank left
      (junctionCount
        (snapshot.withTwoBoundaryTemporaryPriority
          left root right ordered rootRank)
        (snapshot.withOneBoundaryTemporaryPriority
          root right (ne_of_gt ordered.2) rootRank)
        tree) :=
  (twoToOneLocalizedJunctionGeometry
    snapshot left root right ordered rootRank).toJunctionChainCertificate tree

/--
Both rank-restoration phases of the canonical temporary-priority route,
assembled without any user-supplied junction list or injection.

The left chain comes from the two-boundary-to-right-boundary transition; the
right chain comes from restoring the remaining boundary to genuine ranks.
Both chains are measured directly in `Snapshot.ofTree comparison`.
-/
noncomputable def canonicalTwoBoundaryRestoration
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right)
    (tree : BST 0 n) :
    TwoBoundaryRestoration comparison left right
      (temporarySnapshot comparison key comparisonRoot
        left right ordered)
      (rightBoundaryTemporarySnapshot comparison key comparisonRoot
        right ordered.2)
      tree := by
  let snapshot := Snapshot.ofTree comparison
  have rootRank :
      snapshot.rank (valuePos key) = 0 :=
    ofTree_rank_valuePos_eq_zero_of_hasRoot
      comparison key comparisonRoot
  exact {
    leftChain :=
      twoToOneJunctionChainCertificate
        snapshot left (valuePos key) right ordered rootRank tree
    rightChain :=
      oneBoundaryJunctionChainCertificate
        snapshot (valuePos key) right (ne_of_gt ordered.2)
          rootRank tree
  }

end Splay.Accounting.WholeSplayRestorationGeometry
