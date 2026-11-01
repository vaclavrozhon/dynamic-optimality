import MultiSplay.ComparatorSuffixMemory
import TangoSquared.Paper20261030.SecondaryAccessRearrangement

/-!
# Physically restoring the structural suffix boundary

The access to a depth prepares every reference interval containing that
depth. Consequently its unique changed structural boundary, if present,
is an actual preferred-path descendant. The existing balanced-component
repair can flip it back with logarithmic cost. This is a physical
restoration proof, rather than an uncharged assignment to the boundary.
-/

namespace MultiSplay.ComparatorSuffix

open TangoSquared
open TangoSquared.Paper20261030
open Secondary (intervalUpdate)
open SecondaryDecomposition
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition

/-- Every interval containing the prepared depth lies on the preferred path. -/
theorem prepared_node {a b : Nat} (reference : DepthTree a b) (bits : DepthSplit → Bool)
    (request : Nat)
    (prepared : ∀ split ∈ reference.nodes, split.lo ≤ request → request ≤ split.hi →
      bits split = decide (split.cut < request))
    {split : DepthSplit} (member : split ∈ reference.nodes)
    (lower : split.lo ≤ request) (upper : request ≤ split.hi) :
    ∃ found : PreferredSplit bits reference, found.split = split := by
  induction reference with
  | leaf a => simp only [DepthTree.nodes, Finset.notMem_empty] at member
  | @node a b cut ha hb left right ihl ihr =>
      simp only [DepthTree.nodes, Finset.mem_insert, Finset.mem_union] at member
      rcases member with rfl | inLeft | inRight
      · exact ⟨⟨⟨a,cut,b⟩,ha,hb,left,right,.refl _⟩,rfl⟩
      · have bounds := left.node_bounds inLeft
        obtain ⟨found,same⟩ := ihl (fun node present lo hi =>
          prepared node (by simp [DepthTree.nodes,present]) lo hi) inLeft
        have bit : bits ⟨a,cut,b⟩ = false := by
          rw [prepared ⟨a,cut,b⟩ (by simp [DepthTree.nodes]) (by exact le_trans bounds.1 lower)
            (by change request ≤ b; omega)]
          change decide (cut < request) = false
          exact decide_eq_false (by omega)
        exact ⟨⟨found.split,found.lo_le_cut,found.cut_lt_hi,found.left,found.right,
          .left ha hb left right _ bit found.below⟩,same⟩
      · have bounds := right.node_bounds inRight
        obtain ⟨found,same⟩ := ihr (fun node present lo hi =>
          prepared node (by simp [DepthTree.nodes,present]) lo hi) inRight
        have bit : bits ⟨a,cut,b⟩ = true := by
          rw [prepared ⟨a,cut,b⟩ (by simp [DepthTree.nodes]) (by change a ≤ request; omega)
            (by exact le_trans upper bounds.2.2.2)]
          change decide (cut < request) = true
          exact decide_eq_true (by omega)
        exact ⟨⟨found.split,found.lo_le_cut,found.cut_lt_hi,found.left,found.right,
          .right ha hb left right _ bit found.below⟩,same⟩

/-- A restoration difference identifies the original changed boundary and
also proves that the current bit is right and lies on the prepared path. -/
theorem restoration_difference {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lo : a ≤ start) (hi : start ≤ b) (request : Nat)
    (memory : DepthSplit → Bool) {split : DepthSplit}
    (member : split ∈ (suffix reference start lo hi).nodes)
    (different : restoreBoundary reference start
      (intervalUpdate request (preference reference start memory)) split ≠
        intervalUpdate request (preference reference start memory) split) :
    ∃ original ∈ boundaryChanges reference start request,
      clip start original = split ∧
      split.lo ≤ request ∧ request ≤ split.hi ∧
      intervalUpdate request (preference reference start memory) split = true ∧
      restoreBoundary reference start (intervalUpdate request (preference reference start memory)) split = false := by
  obtain ⟨original,present,lookup,same⟩ := suffix_original_lookup reference start lo hi member
  have structural : original.lo < start := by
    by_contra genuine
    exact different (by simp only [restoreBoundary,lookup,if_neg genuine])
  have old : preference reference start memory split = false := by
    simp only [preference,lookup,if_pos structural]
  have restored : restoreBoundary reference start
      (intervalUpdate request (preference reference start memory)) split = false := by
    simp only [restoreBoundary,lookup,if_pos structural]
  have updated : intervalUpdate request (preference reference start memory) split = true := by
    rw [restored] at different
    cases value : intervalUpdate request (preference reference start memory) split <;> simp_all
  have inside : split.lo ≤ request ∧ request ≤ split.hi := by
    by_contra outside
    simp only [intervalUpdate,if_neg outside,old] at updated
    contradiction
  have retained : start ≤ original.cut := by
    have bounds := (suffix reference start lo hi).node_bounds member
    have cuts : original.cut = split.cut := by simpa only [clip_cut] using congrArg DepthSplit.cut same
    omega
  have changed : intervalUpdate request (preference reference start memory) (clip start original) ≠
      preference reference start memory (clip start original) := by
    rw [same,updated,old]
    decide
  exact ⟨original,changed_boundary_mem reference start request memory present retained structural changed,
    same,inside.1,inside.2,updated,restored⟩

theorem restoration_differences_unique {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lo : a ≤ start) (hi : start ≤ b) (request : Nat)
    (memory : DepthSplit → Bool) {first second : DepthSplit}
    (firstMember : first ∈ (suffix reference start lo hi).nodes)
    (secondMember : second ∈ (suffix reference start lo hi).nodes)
    (firstDiff : restoreBoundary reference start
      (intervalUpdate request (preference reference start memory)) first ≠
        intervalUpdate request (preference reference start memory) first)
    (secondDiff : restoreBoundary reference start
      (intervalUpdate request (preference reference start memory)) second ≠
        intervalUpdate request (preference reference start memory) second) : first = second := by
  obtain ⟨one,oneMember,oneEq,_⟩ := restoration_difference reference start lo hi request memory firstMember firstDiff
  obtain ⟨two,twoMember,twoEq,_⟩ := restoration_difference reference start lo hi request memory secondMember secondDiff
  have same := boundaryChanges_subsingleton reference start request one oneMember two twoMember
  exact oneEq.symm.trans ((congrArg (clip start) same).trans twoEq)

/-- The boundary is restored using at most one actual balanced repair. All
genuine memory bits have exactly the values produced by `writeGenuine`. -/
theorem restore_charged {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lo : a ≤ start) (hi : start ≤ b) (request : Nat)
    (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (source (suffix reference start lo hi)
        (intervalUpdate request (preference reference start memory))) component) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight
        (source (suffix reference start lo hi)
          (preference reference start (writeGenuine start request memory))) out ∧
      SourcePointer.Rearranges (closed component) (closed out)
        (19665 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 266) := by
  let induced := suffix reference start lo hi
  let bits := intervalUpdate request (preference reference start memory)
  let restored := restoreBoundary reference start bits
  have restoredSource : source induced restored =
      source induced (preference reference start (writeGenuine start request memory)) := by
    apply source_congr
    intro split member
    exact restore_access_eq reference start lo hi request memory member
  by_cases existsChanged : ∃ split ∈ induced.nodes, restored split ≠ bits split
  · obtain ⟨split,member,different⟩ := existsChanged
    obtain ⟨original,originalMember,same,lower,upper,updated,restoredBit⟩ :=
      restoration_difference reference start lo hi request memory member different
    have prepared : ∀ node ∈ induced.nodes, node.lo ≤ request → request ≤ node.hi →
        bits node = decide (node.cut < request) := by
      intro node _ lower upper
      exact if_pos (show node.lo ≤ request ∧ request ≤ node.hi from ⟨lower,upper⟩)
    obtain ⟨found,foundSplit⟩ := prepared_node induced bits request prepared member lower upper
    have sourceSame : source induced (Function.update bits found.split (!bits found.split)) =
        source induced restored := by
      apply source_congr
      intro node nodeMember
      by_cases selected : node = split
      · subst node
        rw [foundSplit,Function.update_self]
        simp only [show bits split = true from updated,show restored split = false from restoredBit,Bool.not_true]
      · rw [Function.update_of_ne (by simpa only [foundSplit] using selected)]
        apply Eq.symm
        by_contra other
        exact selected (restoration_differences_unique reference start lo hi request memory
          nodeMember member other different)
    obtain ⟨out,outRep,run⟩ := flip_descendant_charged found.lo_le_cut found.cut_lt_hi
      found.left found.right induced bits found.below component represented
    rw [sourceSame,restoredSource] at outRep
    refine ⟨out,outRep,run.mono ?_⟩
    have height := suffix_height reference start lo hi
    have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right height 1)
    dsimp only [induced]
    omega
  · have sourceSame : source induced bits = source induced restored := by
      apply source_congr
      intro split member
      exact (not_ne_iff.mp (fun different => existsChanged ⟨split,member,different⟩)).symm
    refine ⟨component,?_,SourcePointer.rearranges_refl _ _⟩
    rw [sourceSame,restoredSource] at represented
    exact represented

/-- A complete source-level suffix access preserves the genuine history and
returns to the same structural-boundary convention. Its extra restoration
cost is one balanced repair, independently of the boundary spine length. -/
theorem access_restore_charged {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lo : a ≤ start) (hi : start ≤ b) (request : Nat)
    (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (source (suffix reference start lo hi) (preference reference start memory)) component) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight
        (source (suffix reference start lo hi)
          (preference reference start (writeGenuine start request memory))) out ∧
      SourcePointer.Rearranges (closed component) (closed out)
        (((Secondary.decodeDepth (suffix reference start lo hi)
          (preference reference start memory)).accessFlips request + 1) * repairBound reference) := by
  obtain ⟨prepared,preparedRep,access⟩ := access_rearrangement
    (suffix reference start lo hi) (preference reference start memory) request component represented
  obtain ⟨out,outRep,restore⟩ := restore_charged reference start lo hi request memory prepared preparedRep
  refine ⟨out,outRep,(access.trans restore).mono ?_⟩
  have height := suffix_height reference start lo hi
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right height 1)
  have repair : repairBound (suffix reference start lo hi) ≤ repairBound reference := by
    unfold repairBound
    omega
  have accessCost := Nat.mul_le_mul_left
    ((Secondary.decodeDepth (suffix reference start lo hi)
      (preference reference start memory)).accessFlips request) repair
  change _ ≤ _
  rw [Nat.add_mul,Nat.one_mul]
  change _ + repairBound reference ≤ _
  omega

end MultiSplay.ComparatorSuffix
