import ChaCha.Paper20261030.SplayAuxiliaryGlobalPortInventories
import ChaCha.Paper20261030.SplayAuxiliarySpliceReference

/-!
# Primary splice with the unchanged descendant inventories

Only the two root auxiliaries contribute to the potential difference.
All descendants are split and concatenated from the original inventories.
The theorem applies to the actual outputs of any exposed ordinary-splay
exchange with the specified exact port words.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage PreferredProjection SecondaryDecomposition
open MultiSplay.Global.Preferred

theorem exchange_inventories {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incoming out parked : RawComponent Nat Nat)
    (activeRep : Decomposition.Represents cutKey followsRight (source reference p) active)
    (incomingRep : Decomposition.Represents cutKey followsRight (suffixSource reference q d valid) incoming)
    (outRep : Decomposition.Represents cutKey followsRight (source reference (Secondary.spliceBits d p q)) out)
    (parkedRep : Decomposition.Represents cutKey followsRight (suffixSource reference p d valid) parked)
    (outPorts : out.portWord =
      active.portWord.take (PathDecomposition.terminalIndex followsRight (source reference p)) ++ incoming.portWord)
    (parkedPorts : parked.portWord =
      active.portWord.drop (PathDecomposition.terminalIndex followsRight (source reference p)))
    {activeTrees incomingTrees : List (RawTree Nat)}
    (activeInventory : Core (referenceState followsRight (source reference p))
      (referenceCuts cutKey (source reference p)) (referenceCuts id active.closed) activeTrees)
    (incomingInventory : Core (referenceState followsRight (suffixSource reference q d valid))
      (referenceCuts cutKey (suffixSource reference q d valid))
        (referenceCuts id incoming.closed) incomingTrees) :
    ∃ outTrees parkedTrees,
      Core (referenceState followsRight (source reference (Secondary.spliceBits d p q)))
        (referenceCuts cutKey (source reference (Secondary.spliceBits d p q)))
          (referenceCuts id out.closed) outTrees ∧
      Core (referenceState followsRight (suffixSource reference p d valid))
        (referenceCuts cutKey (suffixSource reference p d valid))
          (referenceCuts id parked.closed) parkedTrees ∧
      forestPotential outTrees + forestPotential parkedTrees + potential active.core + potential incoming.core =
        forestPotential activeTrees + forestPotential incomingTrees + potential out.core + potential parked.core := by
  obtain ⟨oldDescendants,oldTrees,oldPorts⟩ := component_inventory_expose
    ((referenceCuts_source_ordered reference p).imp (fun less => Nat.ne_of_lt less)) activeRep activeInventory
  obtain ⟨newDescendants,newTrees,newPorts⟩ := component_inventory_expose
    (referenceCuts_suffix_nodup reference q d valid) incomingRep incomingInventory
  let index := PathDecomposition.terminalIndex followsRight (source reference p)
  let refs := sourcePorts followsRight (source reference p)
  let physical := active.portWord.map (referenceCuts id)
  have sameLength : refs.length = physical.length := oldPorts.length
  have divided : PortInventory cutKey followsRight (refs.take index ++ refs.drop index)
      (physical.take index ++ physical.drop index) oldDescendants := by
    simpa only [List.take_append_drop] using oldPorts
  obtain ⟨front,back,descendants,first,last⟩ := PortInventory.split divided
    (by simp only [List.length_take,sameLength])
  have parkedChildren : PortInventory cutKey followsRight
      (sourcePorts followsRight (suffixSource reference p d valid))
      (parked.portWord.map (referenceCuts id)) back := by
    rw [suffix_sourcePorts reference p d valid preparedP,parkedPorts,List.map_drop]
    exact last
  have outChildren : PortInventory cutKey followsRight
      (sourcePorts followsRight (source reference (Secondary.spliceBits d p q)))
      (out.portWord.map (referenceCuts id)) (front++newDescendants) := by
    rw [source_splice reference p q d valid,splice_sourcePorts reference p q d valid preparedP preparedQ,
      outPorts,List.map_append,List.map_take]
    exact first.append newPorts
  refine ⟨rootPart out.core ++ (front++newDescendants),rootPart parked.core ++ back,
    component_inventory_of_ports outRep outChildren,component_inventory_of_ports parkedRep parkedChildren,?_⟩
  rw [oldTrees,newTrees,descendants]
  simp only [forestPotential_append,forestPotential_rootPart]
  omega

end ChaCha.Paper20261030.SplayAuxiliary
