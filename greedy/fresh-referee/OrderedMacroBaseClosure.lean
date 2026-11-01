import OrderedBaseInvariant
import OrderedRankMacro

/-!
Numerical invariant closure of complete comparator and fixed-rank macros.
Together with their structural specifications these give reusable states;
no invalid owner/base intermediate is exposed as a completed state.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open GreedyMerge.BlockCoverage (Represented Sound Complete)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

theorem reparentSelected_bases {n : ℕ} (comparator beforeTree afterTree : BST 0 n)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key=record.val)
    (ports : List (External n)) (distinct : ports.Nodup)
    (parentPreserved : ∀ record, record ∉ ports →
      canonicalParent (Snapshot.ofTree comparator) afterTree record =
        canonicalParent (Snapshot.ofTree comparator) beforeTree record)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree comparator) beforeTree states)
    (bases : ∀ owner side, BasesValid comparator.externalDepth owner.val (states owner side)) :
    ∀ owner side, BasesValid comparator.externalDepth owner.val
      ((reparentSelected comparator afterTree families ids paidNames makeEntry ports states).1 owner side) := by
  let detached := detachPorts comparator families ids (ports.map Fin.val) 0 states
  have detachedValid := detachPorts_valid comparator families ids (ports.map Fin.val) 0 states valid
  have avoids : ∀ owner side entry, entry ∈ entries (detached.1 owner side) → entry.key ∉ ports.map Fin.val := by
    intro owner side entry member
    exact (detachPorts_membership comparator families ids (ports.map Fin.val) 0 states owner side entry).mp member |>.2
  have detachedSound : Sound (Snapshot.ofTree comparator) afterTree detached.1 := by
    intro owner side entry member
    have oldMember := (detachPorts_membership comparator families ids (ports.map Fin.val) 0 states owner side entry).mp member |>.1
    obtain ⟨record,equal,parent⟩ := sound owner side entry oldMember
    refine ⟨record,equal,?_⟩
    rw [parentPreserved record,parent]
    intro selected
    exact avoids owner side entry member (List.mem_map.mpr ⟨record,selected,equal⟩)
  have absent : ∀ record ∈ ports, ¬ Represented detached.1 record.val := by
    intro record selected ⟨owner,side,entry,member,equal⟩
    exact avoids owner side entry member (List.mem_map.mpr ⟨record,selected,equal.symm⟩)
  exact restorePorts_bases comparator afterTree paidNames makeEntry key ports distinct 0 detached.1
    detachedValid detachedSound absent (detachPorts_bases comparator beforeTree families ids (ports.map Fin.val) 0 states bases sound)

theorem administerRefinementRotation_bases {n depth : ℕ} (comparator : BST 0 n)
    {beforeTree afterTree : BST 0 n} (rotation : RotationAt depth beforeTree afterTree)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key=record.val)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree comparator) beforeTree states)
    (bases : ∀ owner side, BasesValid comparator.externalDepth owner.val (states owner side)) :
    ∀ owner side, BasesValid comparator.externalDepth owner.val
      ((administerRefinementRotation comparator rotation families ids paidNames makeEntry states).1 owner side) := by
  have ports := refinementRotationPorts_spec (Snapshot.ofTree comparator) rotation
  exact reparentSelected_bases comparator beforeTree afterTree families ids paidNames makeEntry key
    _ ports.1 ports.2.2 states valid sound bases

theorem administerJunction_bases {n a b depth treeDepth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (profile : RotationCutProfile before after depth)
    (tree : BST 0 n) (node : AtNode n)
    (occurrence : SubtreeAt (.node node.left node.right) treeDepth tree)
    (separated : ComparatorOuter.Separated node (2*a+1) (2*b+1))
    (oldOwner newOwner : External n)
    (oldValue : oldOwner.val=2*a+1) (newValue : newOwner.val=2*b+1)
    (oldRoot : subtreeOwner (Snapshot.ofTree before) (.node node.left node.right) occurrence.bounds.2=oldOwner)
    (newRoot : subtreeOwner (Snapshot.ofTree after) (.node node.left node.right) occurrence.bounds.2=newOwner)
    (different : oldOwner≠newOwner) (families ids : NameSupply n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key=record.val)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree before) tree states)
    (complete : Complete (Snapshot.ofTree before) tree states)
    (persistent : PersistentGrowers states)
    (upper : ∀ owner side, UpperBase before.externalDepth (states owner side)) :
    ∀ owner side, BasesValid after.externalDepth owner.val
      ((administerJunction profile tree families ids node oldOwner newOwner bulkFresh paidNames makeEntry states).1 owner side) := by
  classical
  let ports := junctionRecords (Snapshot.ofTree before) node
  let prepared := prepareComparator profile families ids (junctionPorts (Snapshot.ofTree before) node)
    {oldOwner,newOwner} states
  let moved := moveJunction oldOwner newOwner node.lower node.upper bulkFresh prepared.1
  let rebased := rebaseAll before after moved
  obtain ⟨movedValid,movedSound,_,movedAbsent,_,_⟩ := prepareMoveJunction_spec step profile tree node occurrence separated
    oldOwner newOwner oldValue newValue oldRoot newRoot different families ids bulkFresh states valid sound complete persistent
  have movedUpper := moveJunction_upperBase before.externalDepth oldOwner newOwner node.lower node.upper bulkFresh prepared.1
    (prepareComparator_upperBase profile tree families ids _ _ states upper sound)
  have movedUniform := moveJunction_uniform (rankShift before after) oldOwner newOwner node.lower node.upper bulkFresh prepared.1
    (prepareComparator_uniform profile families ids _ _ states valid)
  have rebasedBases := (rebaseAll_numeric before after tree moved movedUpper movedSound movedUniform).1
  have rebasedValid := rebaseAll_valid before after moved movedValid
  have rebasedSound := rebaseAll_sound before after tree moved movedSound
  have absent : ∀ record ∈ ports, ¬ Represented rebased record.val := by
    intro record member ⟨owner,side,entry,entryMem,equal⟩
    apply movedAbsent record.val (List.mem_map.mpr ⟨record,member,rfl⟩)
    exact ⟨owner,side,entry,by change entry ∈ entries (moved owner side); simpa only [rebased,rebaseAll_entries] using entryMem,equal⟩
  exact restorePorts_bases after tree paidNames makeEntry key ports (junctionRecords_distinct _ _) 0 rebased
    rebasedValid rebasedSound absent rebasedBases

#print axioms reparentSelected_bases
#print axioms administerRefinementRotation_bases
#print axioms administerJunction_bases

end GreedyMerge.OrderedBlocks
