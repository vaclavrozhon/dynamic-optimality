import Splay.Accounting.JunctionBendReduction
import Splay.Accounting.NormalFormChronologicalBendHistory
import Splay.Assumptions.StructuralNormalForm
import Splay.Rank.TemporaryBoundarySnapshot

namespace Splay.Accounting.WholeSplayTemporaryPriorityReduction

open Splay.Rank
open Splay.Tree.BST
open Splay.Assumptions.NormalForm
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.JunctionBendReduction
open Splay.Lazy.Canonical

/--
The genuine comparison-tree snapshot gives the accessed value rank zero when
the comparison tree serves that value at its root.
-/
theorem ofTree_rank_valuePos_eq_zero_of_hasRoot
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val) :
    (Snapshot.ofTree comparison).rank (valuePos key) = 0 := by
  rw [ofTree_rank_valuePos_eq_depth]
  exact Splay.Tree.BST.depth_eq_zero_of_hasRoot root

/--
Pure rank doubling changes no bend identity in any indexed splay-tree shape.
-/
theorem bendsFrom_withTruePriority_eq
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    bendsFrom snapshot.withTruePriority tree upper_le_n incoming =
      bendsFrom snapshot tree upper_le_n incoming := by
  induction tree generalizing incoming with
  | empty boundary =>
      simp [bendsFrom]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have branchEq :
          node.heavyBranch snapshot.withTruePriority =
            node.heavyBranch snapshot := by
        exact heavyBranch_withTruePriority_eq
          snapshot node.wholeLower node.wholeUpper
            node.whole_nonempty node.root
      simp only [bendsFrom]
      change
        bendAt ⟨root, by
            have bounds := right.lower_le_upper
            omega⟩ incoming (node.heavyBranch snapshot.withTruePriority) ∪
            (bendsFrom snapshot.withTruePriority left (by
                have bounds := right.lower_le_upper
                omega)
              (childIncoming
                (node.heavyBranch snapshot.withTruePriority) .left) ∪
              bendsFrom snapshot.withTruePriority right upper_le_n
                (childIncoming
                  (node.heavyBranch snapshot.withTruePriority) .right)) =
          bendAt ⟨root, by
              have bounds := right.lower_le_upper
              omega⟩ incoming (node.heavyBranch snapshot) ∪
            (bendsFrom snapshot left (by
                have bounds := right.lower_le_upper
                omega)
              (childIncoming (node.heavyBranch snapshot) .left) ∪
              bendsFrom snapshot right upper_le_n
                (childIncoming (node.heavyBranch snapshot) .right))
      rw [branchEq, ihLeft, ihRight]

/-- Complete-tree form: doubled true ranks select exactly the same bends. -/
theorem bends_withTruePriority_eq
    {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) :
    bends snapshot.withTruePriority tree = bends snapshot tree := by
  exact bendsFrom_withTruePriority_eq
    snapshot tree (Nat.le_refl n) none

/--
Canonical temporary snapshot for two selected boundary minima around a served
value.

`TemporaryBoundarySnapshot` proves that this is an actual `Snapshot`, not
merely an order-valued function: every nonempty interval still has a unique
minimum.
-/
def temporarySnapshot
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right) :
    Snapshot n :=
  (Snapshot.ofTree comparison).withTwoBoundaryTemporaryPriority
    left (valuePos key) right ordered
    (ofTree_rank_valuePos_eq_zero_of_hasRoot comparison key root)

@[simp]
theorem temporarySnapshot_rank
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right) :
    (temporarySnapshot comparison key root left right ordered).rank =
      twoBoundaryTemporaryRank
        (Snapshot.ofTree comparison) left right :=
  rfl

/--
Canonical intermediate snapshot after restoring the left boundary while the
right boundary still has artificial priority.
-/
def rightBoundaryTemporarySnapshot
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (right : External n)
    (rightOfRoot : valuePos key < right) :
    Snapshot n :=
  (Snapshot.ofTree comparison).withOneBoundaryTemporaryPriority
    (valuePos key) right
    (by
      intro equal
      have values := congrArg Fin.val equal
      have less : (valuePos key).val < right.val := rightOfRoot
      omega)
    (ofTree_rank_valuePos_eq_zero_of_hasRoot comparison key root)

@[simp]
theorem rightBoundaryTemporarySnapshot_rank
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (right : External n)
    (rightOfRoot : valuePos key < right) :
    (rightBoundaryTemporarySnapshot comparison key root
      right rightOfRoot).rank =
        oneBoundaryTemporaryRank (Snapshot.ofTree comparison) right :=
  rfl

/--
The proof-relevant definition of the manuscript's selected `x⁻` and `x⁺`.

Each selected element is a true-rank minimum of an interval containing the
corresponding adjacent null.  The intervals themselves are left abstract so
that a future tree-focus theorem can instantiate them with the accessed
node's left and right child subtrees.
-/
structure BoundaryMinimumSelection
    {n : ℕ} (snapshot : Snapshot n) (key : Fin n) : Type where
  left : External n
  right : External n
  ordered :
    left < valuePos key ∧ valuePos key < right
  leftLower : External n
  leftUpper : External n
  leftMinimum :
    IsIntervalMin snapshot.rank leftLower leftUpper left
  leftNeighbor_mem :
    leftLower ≤ leftNullPos key ∧ leftNullPos key ≤ leftUpper
  rightLower : External n
  rightUpper : External n
  rightMinimum :
    IsIntervalMin snapshot.rank rightLower rightUpper right
  rightNeighbor_mem :
    rightLower ≤ rightNullPos key ∧ rightNullPos key ≤ rightUpper

namespace BoundaryMinimumSelection

/-- The selected left minimum is no deeper than the adjacent left null. -/
theorem left_rank_le_neighbor
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    (selection : BoundaryMinimumSelection snapshot key) :
    snapshot.rank selection.left ≤ snapshot.rank (leftNullPos key) :=
  selection.leftMinimum.2.2 _
    selection.leftNeighbor_mem.1 selection.leftNeighbor_mem.2

/-- The selected right minimum is no deeper than the adjacent right null. -/
theorem right_rank_le_neighbor
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    (selection : BoundaryMinimumSelection snapshot key) :
    snapshot.rank selection.right ≤ snapshot.rank (rightNullPos key) :=
  selection.rightMinimum.2.2 _
    selection.rightNeighbor_mem.1 selection.rightNeighbor_mem.2

end BoundaryMinimumSelection

/--
A proof-relevant count of restoration junctions embedded into a genuine
bottom-to-top heap-ancestor chain.

The missing geometric statement is now explicit: every relevant junction
must occupy a distinct position of the chain.  Once that is supplied, the
rank bound gives the numerical budget automatically.
-/
structure JunctionChainCertificate
    {n : ℕ} (rank : External n → ℕ)
    (first : External n) (junctions : ℕ) : Type where
  ancestors : List (External n)
  chain :
    IsHeapAncestorChain rank (first :: ancestors)
  junctions_le_length :
    junctions ≤ (first :: ancestors).length

namespace JunctionChainCertificate

/-- A certified junction chain has at most `rank(first) + 1` members. -/
theorem junctions_le_rank_succ
    {n : ℕ} {rank : External n → ℕ}
    {first : External n} {junctions : ℕ}
    (certificate :
      JunctionChainCertificate rank first junctions) :
    junctions ≤ rank first + 1 := by
  exact certificate.junctions_le_length.trans
    (heapAncestorChain_length_le_rank_succ
      rank first certificate.ancestors certificate.chain)

/-- A rank bound turns the chain length into the advertised uniform budget. -/
theorem junctions_le
    {n : ℕ} {rank : External n → ℕ}
    {first : External n} {junctions bound : ℕ}
    (certificate :
      JunctionChainCertificate rank first junctions)
    (rank_le : rank first ≤ bound) :
    junctions ≤ bound + 1 :=
  certificate.junctions_le_rank_succ.trans
    (Nat.add_le_add_right rank_le 1)

end JunctionChainCertificate

/--
The two rank-restoration phases after the artificial-priority splay.

The first phase restores the selected left boundary, producing `afterLeft`;
the second restores the right boundary and reaches the genuine comparison
snapshot.  Each actual heavy-branch junction of the fixed final splay-tree
shape is assigned to the appropriate low-rank heap-ancestor chain.
-/
structure TwoBoundaryRestoration
    {n : ℕ} (comparison : BST 0 n)
    (left right : External n)
    (artificial afterLeft : Snapshot n)
    (tree : BST 0 n) : Type where
  leftChain :
    JunctionChainCertificate
      (Snapshot.ofTree comparison).rank left
      (junctionCount artificial afterLeft tree)
  rightChain :
    JunctionChainCertificate
      (Snapshot.ofTree comparison).rank right
      (junctionCount afterLeft (Snapshot.ofTree comparison) tree)

namespace TwoBoundaryRestoration

/-- Bend creations in the two exact restoration transitions. -/
noncomputable def created
    {n : ℕ} {comparison : BST 0 n}
    {left right : External n}
    {artificial afterLeft : Snapshot n}
    {tree : BST 0 n}
    (_certificate :
      TwoBoundaryRestoration comparison left right
        artificial afterLeft tree) : ℕ :=
  ((bends afterLeft tree) \ (bends artificial tree)).card +
    ((bends (Snapshot.ofTree comparison) tree) \
      (bends afterLeft tree)).card

/-- Bend removals in the two exact restoration transitions. -/
noncomputable def removed
    {n : ℕ} {comparison : BST 0 n}
    {left right : External n}
    {artificial afterLeft : Snapshot n}
    {tree : BST 0 n}
    (_certificate :
      TwoBoundaryRestoration comparison left right
        artificial afterLeft tree) : ℕ :=
  ((bends artificial tree) \ (bends afterLeft tree)).card +
    ((bends afterLeft tree) \
      (bends (Snapshot.ofTree comparison) tree)).card

/--
Two low-rank restoration chains create at most
`6 * (bound + 1)` bends: two chains, at most `bound + 1` junctions per
chain, and at most three bends per junction.
-/
theorem created_le_six_mul_rank_succ
    {n bound : ℕ} {comparison : BST 0 n}
    {left right : External n}
    {artificial afterLeft : Snapshot n}
    {tree : BST 0 n}
    (certificate :
      TwoBoundaryRestoration comparison left right
        artificial afterLeft tree)
    (leftRank :
      (Snapshot.ofTree comparison).rank left ≤ bound)
    (rightRank :
      (Snapshot.ofTree comparison).rank right ≤ bound) :
    certificate.created ≤ 6 * (bound + 1) := by
  have leftJunctions :=
    certificate.leftChain.junctions_le leftRank
  have rightJunctions :=
    certificate.rightChain.junctions_le rightRank
  have leftCreated :=
    created_le_three_mul_junctionCount
      artificial afterLeft tree
  have rightCreated :=
    created_le_three_mul_junctionCount
      afterLeft (Snapshot.ofTree comparison) tree
  unfold created
  omega

end TwoBoundaryRestoration

/--
The exact remaining geometry for the manuscript's temporary-priority route.

This certificate deliberately talks about the conceptual three-phase path,
not the stronger fixed-genuine-snapshot substep history:

1. installing the artificial boundary priorities does not change the initial
   bend set;
2. the complete splay under those priorities creates at most one bend per
   zig-zig plus `coreBudget`, and removes at least one per zig-zag;
3. restoring the two true boundary ranks follows the two certified junction
   chains.

The low true ranks of the selected boundary minima are stated relative to the
adjacent nulls.  A serving comparison root plus
`HasRelevantNeighborRankBound` therefore discharges their uniform bound.
-/
structure TemporarySplayBendCertificate
    (constants : BendConstants)
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (transcript : SplayExecutionTranscriptWitness execution)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right)
    (afterLeft : Snapshot n)
    (coreBudget : ℕ) : Type where
  before_bends_eq :
    bends (Snapshot.ofTree comparison) before =
      bends
        (temporarySnapshot comparison key comparisonRoot
          left right ordered) before
  core_created_le :
    ((bends
        (temporarySnapshot comparison key comparisonRoot
          left right ordered) after) \
      (bends
        (temporarySnapshot comparison key comparisonRoot
          left right ordered) before)).card ≤
        transcript.zigZig + coreBudget
  core_removed_ge :
    transcript.zigZag ≤
      ((bends
          (temporarySnapshot comparison key comparisonRoot
            left right ordered) before) \
        (bends
          (temporarySnapshot comparison key comparisonRoot
            left right ordered) after)).card
  left_rank_le_neighbor :
    (Snapshot.ofTree comparison).rank left ≤
      (Snapshot.ofTree comparison).rank (leftNullPos key)
  right_rank_le_neighbor :
    (Snapshot.ofTree comparison).rank right ≤
      (Snapshot.ofTree comparison).rank (rightNullPos key)
  restoration :
    TwoBoundaryRestoration comparison left right
      (temporarySnapshot comparison key comparisonRoot
        left right ordered)
      afterLeft after

namespace TemporarySplayBendCertificate

/--
Build the residual certificate from actual boundary interval minima.

This constructor discharges both low-boundary-rank fields; only the three
genuinely structural splay facts remain explicit: preprocessing invisibility,
the temporary-priority core bend bounds, and the restoration chains.
-/
def ofBoundaryMinima
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    (selection :
      BoundaryMinimumSelection (Snapshot.ofTree comparison) key)
    {afterLeft : Snapshot n} {coreBudget : ℕ}
    (before_bends_eq :
      bends (Snapshot.ofTree comparison) before =
        bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered) before)
    (core_created_le :
      ((bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered) after) \
        (bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered) before)).card ≤
          transcript.zigZig + coreBudget)
    (core_removed_ge :
      transcript.zigZag ≤
        ((bends
            (temporarySnapshot comparison key comparisonRoot
              selection.left selection.right selection.ordered) before) \
          (bends
            (temporarySnapshot comparison key comparisonRoot
              selection.left selection.right selection.ordered) after)).card)
    (restoration :
      TwoBoundaryRestoration comparison selection.left selection.right
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)
        afterLeft after) :
    TemporarySplayBendCertificate constants comparison key execution
      comparisonRoot transcript selection.left selection.right
      selection.ordered afterLeft coreBudget where
  before_bends_eq := before_bends_eq
  core_created_le := core_created_le
  core_removed_ge := core_removed_ge
  left_rank_le_neighbor := selection.left_rank_le_neighbor
  right_rank_le_neighbor := selection.right_rank_le_neighbor
  restoration := restoration

/-- Exact created count along core-splay and both restoration phases. -/
noncomputable def created
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    {afterLeft : Snapshot n} {coreBudget : ℕ}
    (certificate :
      TemporarySplayBendCertificate constants comparison key execution
        comparisonRoot transcript left right ordered afterLeft
        coreBudget) : ℕ :=
  ((bends
      (temporarySnapshot comparison key comparisonRoot
        left right ordered) after) \
    (bends
      (temporarySnapshot comparison key comparisonRoot
        left right ordered) before)).card +
    certificate.restoration.created

/-- Exact removed count along core-splay and both restoration phases. -/
noncomputable def removed
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    {afterLeft : Snapshot n} {coreBudget : ℕ}
    (certificate :
      TemporarySplayBendCertificate constants comparison key execution
        comparisonRoot transcript left right ordered afterLeft
        coreBudget) : ℕ :=
  ((bends
      (temporarySnapshot comparison key comparisonRoot
        left right ordered) before) \
    (bends
      (temporarySnapshot comparison key comparisonRoot
        left right ordered) after)).card +
    certificate.restoration.removed

/-- The conceptual path aggregated into exactly one complete-splay action. -/
noncomputable def action
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    {afterLeft : Snapshot n} {coreBudget : ℕ}
    (certificate :
      TemporarySplayBendCertificate constants comparison key execution
        comparisonRoot transcript left right ordered afterLeft
        coreBudget) : BendAction where
  kind := .splay
  zigZig := transcript.zigZig
  zigZag := transcript.zigZag
  created := certificate.created
  removed := certificate.removed

/--
The conceptual core and restoration transitions telescope between the true
comparison-snapshot endpoint bend counts.
-/
theorem history
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    {afterLeft : Snapshot n} {coreBudget : ℕ}
    (certificate :
      TemporarySplayBendCertificate constants comparison key execution
        comparisonRoot transcript left right ordered afterLeft
        coreBudget) :
    BendHistory
      (bends (Snapshot.ofTree comparison) before).card
      [certificate.action]
      (bends (Snapshot.ofTree comparison) after).card := by
  let artificial :=
    temporarySnapshot comparison key comparisonRoot left right ordered
  let coreAction :=
    BendAction.between .splay transcript.zigZig transcript.zigZag
      (bends artificial before) (bends artificial after)
  let leftAction :=
    BendAction.between .splay 0 0
      (bends artificial after) (bends afterLeft after)
  let rightAction :=
    BendAction.between .splay 0 0
      (bends afterLeft after) (bends (Snapshot.ofTree comparison) after)
  have coreBalance :=
    BendAction.card_balance_between .splay
      transcript.zigZig transcript.zigZag
      (bends artificial before) (bends artificial after)
  have leftBalance :=
    BendAction.card_balance_between .splay 0 0
      (bends artificial after) (bends afterLeft after)
  have rightBalance :=
    BendAction.card_balance_between .splay 0 0
      (bends afterLeft after) (bends (Snapshot.ofTree comparison) after)
  refine .cons certificate.action [] ?_ (.nil _)
  change
    (bends (Snapshot.ofTree comparison) before).card +
        certificate.created =
      (bends (Snapshot.ofTree comparison) after).card +
        certificate.removed
  rw [certificate.before_bends_eq]
  change
    (bends artificial before).card + certificate.created =
      (bends (Snapshot.ofTree comparison) after).card +
        certificate.removed
  simp only [created, removed, TwoBoundaryRestoration.created,
    TwoBoundaryRestoration.removed]
  dsimp only [coreAction, leftAction, rightAction,
    BendAction.between] at coreBalance leftBalance rightBalance
  dsimp only [artificial] at coreBalance leftBalance rightBalance ⊢
  omega

/-- The core removal clause survives aggregation with restoration removals. -/
theorem zigZag_le_removed
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    {afterLeft : Snapshot n} {coreBudget : ℕ}
    (certificate :
      TemporarySplayBendCertificate constants comparison key execution
        comparisonRoot transcript left right ordered afterLeft
        coreBudget) :
    transcript.zigZag ≤ certificate.removed := by
  unfold removed
  exact certificate.core_removed_ge.trans (Nat.le_add_right _ _)

/--
The serving-root neighbor bound controls both selected boundary ranks.
-/
theorem boundaryRanks_le
    {constants : BendConstants}
    {n slack : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    {afterLeft : Snapshot n} {coreBudget : ℕ}
    (certificate :
      TemporarySplayBendCertificate constants comparison key execution
        comparisonRoot transcript left right ordered afterLeft
        coreBudget)
    (neighborBound :
      HasRelevantNeighborRankBound
        (Snapshot.ofTree comparison) slack) :
    (Snapshot.ofTree comparison).rank left ≤ slack ∧
      (Snapshot.ofTree comparison).rank right ≤ slack := by
  have neighbors := neighborBound key
  have rootRank :=
    ofTree_rank_valuePos_eq_zero_of_hasRoot
      comparison key comparisonRoot
  rw [rootRank, Nat.zero_add] at neighbors
  exact
    ⟨certificate.left_rank_le_neighbor.trans neighbors.1,
      certificate.right_rank_le_neighbor.trans neighbors.2⟩

/--
The numerical manuscript bound:

`coreBudget + 6 * (neighborRankBound + 1)`

is a sufficient once-per-access splay allowance.
-/
theorem action_locallySound
    {constants : BendConstants}
    {n slack : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    {afterLeft : Snapshot n} {coreBudget : ℕ}
    (certificate :
      TemporarySplayBendCertificate constants comparison key execution
        comparisonRoot transcript left right ordered afterLeft
        coreBudget)
    (neighborBound :
      HasRelevantNeighborRankBound
        (Snapshot.ofTree comparison) slack)
    (allowance :
      coreBudget + 6 * (slack + 1) ≤ constants.splay) :
    certificate.action.LocallySound constants := by
  have ranks := certificate.boundaryRanks_le neighborBound
  have restorationCreated :=
    certificate.restoration.created_le_six_mul_rank_succ
      ranks.1 ranks.2
  change
    transcript.zigZag ≤ certificate.removed ∧
      certificate.created ≤ transcript.zigZig + constants.splay
  constructor
  · exact certificate.zigZag_le_removed
  · unfold created
    have coreCreated := certificate.core_created_le
    omega

/--
Direct adapter to the normal-form schedule API.  The global scheduler sees
one locally sound action whose numerical history has the genuine
comparison-snapshot endpoints; all temporary snapshots remain internal.
-/
noncomputable def toCompleteSplayCertificate
    {constants : BendConstants}
    {n slack : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    {afterLeft : Snapshot n} {coreBudget : ℕ}
    (certificate :
      TemporarySplayBendCertificate constants comparison key execution
        comparisonRoot transcript left right ordered afterLeft
        coreBudget)
    (neighborBound :
      HasRelevantNeighborRankBound
        (Snapshot.ofTree comparison) slack)
    (allowance :
      coreBudget + 6 * (slack + 1) ≤ constants.splay) :
    NormalFormChronologicalBendHistory.CompleteSplayCertificate
      constants comparison key execution :=
  NormalFormChronologicalBendHistory.CompleteSplayCertificate.ofAction
    comparisonRoot transcript certificate.action certificate.history
    (certificate.action_locallySound neighborBound allowance)
    rfl rfl rfl

/--
Manuscript-strength specialization: before rank restoration, at most two
administrative bends are created in addition to one per zig-zig.
-/
abbrev CoreTwoCertificate
    (constants : BendConstants)
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (transcript : SplayExecutionTranscriptWitness execution)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right)
    (afterLeft : Snapshot n) :=
  TemporarySplayBendCertificate constants comparison key execution
    comparisonRoot transcript left right ordered afterLeft 2

/--
Core-budget-two certificate using the canonical one-boundary intermediate
snapshot.  Thus both auxiliary snapshots are now constructed automatically;
no snapshot-existence premise remains.
-/
abbrev CanonicalCoreTwoCertificate
    (constants : BendConstants)
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (transcript : SplayExecutionTranscriptWitness execution)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right) :=
  CoreTwoCertificate constants comparison key execution
    comparisonRoot transcript left right ordered
    (rightBoundaryTemporarySnapshot comparison key comparisonRoot
      right ordered.2)

/--
With core budget two, the explicit complete-splay allowance is
`2 + 6 * (slack + 1)`.
-/
noncomputable def CoreTwoCertificate.toCompleteSplayCertificate
    {constants : BendConstants}
    {n slack : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    {afterLeft : Snapshot n}
    (certificate :
      CoreTwoCertificate constants comparison key execution
        comparisonRoot transcript left right ordered afterLeft)
    (neighborBound :
      HasRelevantNeighborRankBound
        (Snapshot.ofTree comparison) slack)
    (allowance :
      2 + 6 * (slack + 1) ≤ constants.splay) :
    NormalFormChronologicalBendHistory.CompleteSplayCertificate
      constants comparison key execution :=
  TemporarySplayBendCertificate.toCompleteSplayCertificate
    certificate neighborBound allowance

/--
Canonical-snapshot specialization of the schedule adapter.
-/
noncomputable def CanonicalCoreTwoCertificate.toCompleteSplayCertificate
    {constants : BendConstants}
    {n slack : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    (certificate :
      CanonicalCoreTwoCertificate constants comparison key execution
        comparisonRoot transcript left right ordered)
    (neighborBound :
      HasRelevantNeighborRankBound
        (Snapshot.ofTree comparison) slack)
    (allowance :
      2 + 6 * (slack + 1) ≤ constants.splay) :
    NormalFormChronologicalBendHistory.CompleteSplayCertificate
      constants comparison key execution :=
  CoreTwoCertificate.toCompleteSplayCertificate
    certificate neighborBound allowance

end TemporarySplayBendCertificate

end Splay.Accounting.WholeSplayTemporaryPriorityReduction
