import ActualSideGeometries
import ActualFamilyCuts
import ConcreteHistoryEdits

/-!
Whole-family creator cuts follow from the original immutable conversion
records and the concrete closed-family edit program. Even whole-block
permutations cannot change the relation between an Entry's key and joined
time. This derives the family-wide monotonicity premise from physical
records, rather than assuming an extra event-to-source cut map.
-/
namespace GreedyMerge.HistoryProcess
open GreedyMerge.OrderedBlocks

theorem Edit.descendants {before after : List Frozen} (edit : Edit before after) :
    ∀ block∈after, ∃ original∈before, Descends block original := by
  cases edit with
  | split pre post focus cut leftId rightId =>
      intro block member
      simp only [List.mem_append] at member
      rcases member with left | piece | right
      · exact ⟨block,by simp [left],descends_refl block⟩
      · exact ⟨focus,by simp,splitFresh_descends leftId rightId focus cut block piece⟩
      · exact ⟨block,by simp [right],descends_refl block⟩
  | erase pre post focus key =>
      intro block member
      simp only [List.mem_append,List.mem_cons] at member
      rcases member with left | rfl | right
      · exact ⟨block,by simp [left],descends_refl block⟩
      · exact ⟨focus,by simp,erase_descends focus key⟩
      · exact ⟨block,by simp [right],descends_refl block⟩
  | rebase pre post focus base =>
      intro block member
      simp only [List.mem_append,List.mem_cons] at member
      rcases member with left | rfl | right
      · exact ⟨block,by simp [left],descends_refl block⟩
      · exact ⟨focus,by simp,rebase_descends focus base⟩
      · exact ⟨block,by simp [right],descends_refl block⟩
  | perm permutation =>
      intro block member
      exact ⟨block,permutation.mem_iff.mp member,descends_refl block⟩

theorem Run.descendants {before after : List Frozen} (run : Run before after) :
    ∀ block∈after, ∃ original∈before, Descends block original := by
  induction run with
  | nil blocks => exact fun block member => ⟨block,member,descends_refl block⟩
  | cons step rest ih =>
      intro block member
      obtain ⟨middle,middleMem,toMiddle⟩ := ih block member
      obtain ⟨original,originalMem,toOriginal⟩ := step.descendants middle middleMem
      exact ⟨original,originalMem,descends_trans toMiddle toOriginal⟩

theorem Run.from_singleton {original : Frozen} {after : List Frozen} (run : Run [original] after) :
    ∀ block∈after, Descends block original := by
  intro block member
  obtain ⟨old,oldMem,descendant⟩ := run.descendants block member
  simpa only [List.mem_singleton.mp oldMem] using descendant

end GreedyMerge.HistoryProcess

namespace GreedyMerge.AccessSourceAccounting
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.ActualBlockPartition
open GreedyForest.Phase

noncomputable def storedFamily (state : SideState) (id : ℕ) : ℕ := by
  classical
  exact if present : ∃ block∈state.shrinking, block.id=id then present.choose.family else 0

theorem storedFamily_of_frozen (state : SideState) (ids : (state.shrinking.map Frozen.id).Nodup)
    (block : Frozen) (member : block∈state.shrinking) : storedFamily state block.id=block.family := by
  have present : ∃ actual∈state.shrinking, actual.id=block.id := ⟨block,member,rfl⟩
  simp only [storedFamily,dif_pos present]
  exact congrArg Frozen.family
    (List.inj_on_of_nodup_map ids present.choose_spec.1 member present.choose_spec.2)

/-- Literal enumeration of all current frozen records. It has no relation
to reserved-name counters or an independently supplied accounting set. -/
noncomputable def heapFrozen {n : ℕ} (states : States n) : List Frozen :=
  (Finset.univ.toList : List (External n × Bool)).flatMap (fun slot => (states slot.1 slot.2).shrinking)

noncomputable def heapFamily {n : ℕ} (states : States n) (family : ℕ) : List Frozen :=
  (heapFrozen states).filter (fun block => block.family==family)

theorem mem_heapFrozen {n : ℕ} (states : States n) (block : Frozen) :
    block∈heapFrozen states ↔ ∃ owner side, block∈(states owner side).shrinking := by
  simp only [heapFrozen,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨owner,side⟩,member⟩
    exact ⟨owner,side,member⟩
  · rintro ⟨owner,side,member⟩
    exact ⟨(owner,side),member⟩

theorem mem_heapFamily {n : ℕ} (states : States n) (family : ℕ) (block : Frozen) :
    block∈heapFamily states family ↔ (∃ owner side, block∈(states owner side).shrinking) ∧ block.family=family := by
  simp only [heapFamily,List.mem_filter,beq_iff_eq,mem_heapFrozen]

/-- Every currently frozen family fragment is an actual Entry subsequence
of the original conversion block, by the literal edit execution. -/
theorem heapFamily_descends {n : ℕ} (states : States n) (original : Frozen)
    (closed : HistoryProcess.Run [original] (heapFamily states original.family))
    (owner : External n) (side : Bool) (block : Frozen) (member : block∈(states owner side).shrinking)
    (sameFamily : block.family=original.family) : Descends block original :=
  closed.from_singleton block ((mem_heapFamily states original.family block).mpr ⟨⟨owner,side,member⟩,sameFamily⟩)

/-- The full family's current source records retain one temporal
orientation in increasing key order, even when split blocks moved between
owners and the global block enumeration was permuted. -/
theorem SideView.storedJoin_family_order {n lo hi : ℕ} {rank : ℕ→ℕ} {initial : ℕ→ℤ} {record : ℕ→ℕ}
    {tree : BST lo hi} (states : States n) (source : External n) (side : Bool)
    (view : SideView rank initial record tree (states source side))
    (valid : Valid source.val side (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (recordMono : ∀ first∈atoms tree, ∀ second∈atoms tree,
      first ≤ second → record first ≤ record second)
    (original : Frozen) (originalSide : Bool)
    (spatial : original.members.Pairwise (OrderedBlocks.outward originalSide))
    (history : ∃ orientation, HistMonotone orientation original.members)
    (closed : HistoryProcess.Run [original] (heapFamily states original.family)) :
    (∀ first∈familyMembers tree view.partition.block (storedFamily (states source side)) original.family,
      ∀ second∈familyMembers tree view.partition.block (storedFamily (states source side)) original.family,
      first ≤ second → storedJoin (states source side) (record first) ≤ storedJoin (states source side) (record second)) ∨
    (∀ first∈familyMembers tree view.partition.block (storedFamily (states source side)) original.family,
      ∀ second∈familyMembers tree view.partition.block (storedFamily (states source side)) original.family,
      first ≤ second → storedJoin (states source side) (record second) ≤ storedJoin (states source side) (record first)) := by
  obtain ⟨orientation,orientedHistory⟩ := increasingMembers_history originalSide original history
  have orientedOrder : (increasingMembers originalSide original).Pairwise
      (fun first second => first.key<second.key) := by
    cases originalSide with
    | false => exact spatial
    | true => exact List.pairwise_reverse.mpr spatial
  have backed : ∀ atom∈familyMembers tree view.partition.block (storedFamily (states source side)) original.family,
      ∃ entry∈original.members, entry.key=record atom ∧ storedJoin (states source side) (record atom)=entry.joined := by
    intro atom atomMem
    obtain ⟨atomRoot,familyEq⟩ := Finset.mem_filter.mp atomMem
    have atomPresent := List.mem_toFinset.mp atomRoot
    have bounds := (atoms_mem_iff tree atom).mp atomPresent
    obtain ⟨block,blockMem,keyMem⟩ := view.covered atom atomPresent
    have blockEq := (view.matching atom bounds.1 bounds.2 block blockMem).mpr keyMem
    have family : block.family=original.family := by
      rw [blockEq,storedFamily_of_frozen _ ids block blockMem] at familyEq
      exact familyEq
    obtain ⟨entry,entryMem,entryKey⟩ := List.mem_map.mp keyMem
    have descendant := heapFamily_descends states original closed source side block blockMem family
    refine ⟨entry,descendant.2.2.subset entryMem,entryKey,?_⟩
    rw [←entryKey]
    exact storedJoin_of_frozen _ source.val side valid block blockMem entry entryMem
  have compare : ∀ first∈familyMembers tree view.partition.block (storedFamily (states source side)) original.family,
      ∀ second∈familyMembers tree view.partition.block (storedFamily (states source side)) original.family,
      first ≤ second →
      if orientation then storedJoin (states source side) (record first) ≤ storedJoin (states source side) (record second)
      else storedJoin (states source side) (record second) ≤ storedJoin (states source side) (record first) := by
    intro first firstMem second secondMem less
    obtain ⟨firstEntry,firstEntryMem,firstKey,firstJoin⟩ := backed first firstMem
    obtain ⟨secondEntry,secondEntryMem,secondKey,secondJoin⟩ := backed second secondMem
    have entryOrder : firstEntry.key ≤ secondEntry.key := by
      rw [firstKey,secondKey]
      exact recordMono first (List.mem_toFinset.mp (Finset.mem_filter.mp firstMem).1)
        second (List.mem_toFinset.mp (Finset.mem_filter.mp secondMem).1) less
    rw [firstJoin,secondJoin]
    exact increasing_history_compare (increasingMembers originalSide original) orientation orientedOrder
      orientedHistory firstEntry secondEntry ((increasingMembers_mem _ _ _).mpr firstEntryMem)
      ((increasingMembers_mem _ _ _).mpr secondEntryMem) entryOrder
  cases orientation with
  | false => exact Or.inr (by simpa only [Bool.false_eq_true,if_false] using compare)
  | true => exact Or.inl (by simpa only [if_true] using compare)

/-- Whole-family cut geometry for the actual family census, with the
unique crossing source and spatial cut constructed internally. -/
theorem SideView.family_cut_geometry {n lo hi : ℕ} {rank : ℕ→ℕ} {initial : ℕ→ℤ} {record : ℕ→ℕ}
    {tree : BST lo hi} (states : States n) (source : External n) (side : Bool)
    (view : SideView rank initial record tree (states source side))
    (valid : Valid source.val side (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (recordMono : ∀ first∈atoms tree, ∀ second∈atoms tree,
      first ≤ second → record first ≤ record second)
    (owner : ℕ→ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (original : Frozen) (originalSide : Bool)
    (spatial : original.members.Pairwise (OrderedBlocks.outward originalSide))
    (history : ∃ orientation, HistMonotone orientation original.members)
    (closed : HistoryProcess.Run [original] (heapFamily states original.family)) (time H : ℕ)
    (bound : ∀ atom, 2*lo ≤ atom → atom ≤ 2*hi → rank (record atom) ≤ H) :
    Nonempty (GreedyForest.Execution.CutPhaseGeometry (contractedGap H)
      (familyBadCrossings (rank ∘ record) (initial ∘ record) (schedule owner tree)
        view.partition.block (storedFamily (states source side)) (storedJoin (states source side) ∘ record)
        original.family time).card) := by
  exact actual_family_cut_geometry _ owner tree projection localOwners _ view.partition _ _ original.family time H
    (view.storedJoin_family_order states source side valid ids recordMono original originalSide spatial history closed) bound

end GreedyMerge.AccessSourceAccounting

#print axioms GreedyMerge.HistoryProcess.Run.descendants
#print axioms GreedyMerge.AccessSourceAccounting.SideView.storedJoin_family_order
#print axioms GreedyMerge.AccessSourceAccounting.SideView.family_cut_geometry
