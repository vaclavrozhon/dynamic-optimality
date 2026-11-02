import MultiSplay.Obstructions.ClassicalPhysical
import MultiSplay.GlobalPreferredHistory

/-! A legal full-primary-state obstruction to the classical MultiSplay
potential analysis. It is a one-access family, not a competitive lower
bound and not a claimed sequence reachable after canonical initialization. -/

namespace MultiSplay.Obstructions.Classical

open DynamicOptimality (RawTree)
open DynamicOptimality.SearchRotation
open ChaCha (DepthTree)
open ChaCha.MTR
open ChaCha.MTR.Tree
open Pointer (MarkedTree)
open ChaCha.Primary (Key)
open ChaCha.Paper20261030
open EndpointEncoding ClassicalSwitch Global Global.Preferred

/-- An arbitrarily large perfect primary reference, an actual path-compatible
physical BST, and one genuine ordinary MultiSplay access. Its root auxiliary
has H nodes; the whole primary reference has 2^H−1 nodes. The complete
persistent forest potential rises, while the primary partition and all
other auxiliaries remain unchanged. -/
 theorem physical_family (s : Nat) (positive : 0 < s) :
    let height := 2^(2*s+1)-1
    ∃ (reference before after : RawTree Nat) (trees next : List (RawTree Nat))
      (address : Key) (pivot cost work : Nat),
      reference = perfect height (2^height) ∧ reference.size = 2^height-1 ∧
      before.Ordered ∧ before.inorder = reference.inorder ∧ after.inorder = reference.inorder ∧
      Core allRight reference before trees ∧ Core (nodeStep allRight address) reference after next ∧
      Switches allRight reference (actualEmissions allRight address) before after (3*s-1) work ∧
      Access pivot before after cost ∧ 3*s-1 ≤ cost ∧
      forestRank trees+(s : ℝ)*Real.logb 2 6 < forestRank next ∧
      ancestorEmissions allRight address = [] ∧ actualEmissions allRight address = [address] ∧
      forest (nodeStep allRight address) reference = forest allRight reference ∧
      Secondary.actualLedger (DepthTree.midpoint 0 height (Nat.zero_le height)) (fun _ => true)
        allRight [address] = 1 := by
  let height := 2^(2*s+1)-1
  have powLarge : 8 ≤ 2^(2*s+1) := by
    have bound := pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 2) (by omega : 3 ≤ 2*s+1)
    simpa using bound
  have heightLarge : 2 ≤ height := by dsimp [height]; omega
  let depth := height-2
  let pivot := 2^height
  let reference := perfect height pivot
  let address := List.replicate (height-1) true
  have heightEq : depth+2 = height := by dsimp [depth]; omega
  have depthEq : depth+1 = height-1 := by dsimp [depth]; omega
  obtain ⟨frontKeys,spine,path,lower,upper,word,prefixLength⟩ := maximum_reference_data depth pivot
  rw [heightEq,depthEq] at path
  rw [heightEq] at word
  change Path allRight reference address spine (.node .empty pivot .empty) at path
  have wordLength : (frontKeys++[pivot-1,pivot]).length = 2^(2*s+1)-1 := by
    simp only [List.length_append,List.length_cons,List.length_nil,prefixLength]
    change depth+2 = height
    exact heightEq
  obtain ⟨auxiliary,left,last,auxiliaryWord,lastWord,first,second,run,gain⟩ :=
    family_on_word s positive frontKeys (pivot-1) pivot wordLength
  obtain ⟨marked,shape,represented,physicalWord⟩ := initial_shape allRight reference auxiliary
    (auxiliaryWord.trans word.symm)
  have ordered : reference.Ordered := perfect_ordered height pivot le_rfl
  have distinct : reference.inorder.Nodup := ordered.imp (fun less => Nat.ne_of_lt less)
  let target := node (node last (pivot-1) empty) pivot empty
  have targetWord : target.inorder = marked.skeleton.inorder := by
    rw [shape,auxiliaryWord]
    simp only [target,inorder,lastWord,List.append_nil,List.append_assoc,List.singleton_append]
  have actualRun : ClassicalSwitch.Execution pivot empty (allRight address) spine.lower spine.upper
      marked.skeleton target empty (3*s-1) := by
    simpa only [allRight,lower,upper,shape,target] using run
  obtain ⟨main,trees,next,work,mainShape,mainRep,inventory,nextInventory,switch,potentialEq⟩ :=
    embed_leaf_execution path distinct represented actualRun targetWord
  have finalState : toggle allRight address = nodeStep allRight address := by
    have final : beforeFinal allRight address = allRight := by simp [beforeFinal,address,right_ancestors,applySwitches]
    simpa only [final] using final_toggle allRight address
  have actualWord : actualEmissions allRight address = [address] := right_emissions _
  have history : Switches allRight reference (actualEmissions allRight address)
      marked.erase main.erase (3*s-1) work := by
    rw [actualWord]
    simpa only [Nat.add_zero] using Switches.cons switch (Switches.nil _ _ _)
  have beforeOrdered : marked.erase.Ordered := by unfold Ordered; rw [physicalWord]; exact ordered
  have present : pivot ∈ marked.erase.inorder := by
    have pathMember : pivot ∈ marked.skeleton.inorder := by rw [shape,auxiliaryWord]; simp
    rw [← marked.graft_gapArray]
    exact (inorder_sublist_graft marked.skeleton marked.gapArray 0).subset pathMember
  obtain ⟨searchDepth,search⟩ := searchDepth_exists_of_mem beforeOrdered present
  let cost := searchDepth+1+(3*s-1)
  have access : Access pivot marked.erase main.erase cost := ⟨searchDepth,3*s-1,search,switch.rotations,rfl⟩
  have globalGain : forestRank trees+(s : ℝ)*Real.logb 2 6 < forestRank next := by
    rw [shape] at potentialEq
    change potential auxiliary+(s : ℝ)*Real.logb 2 6 < potential target at gain
    linarith
  have allLedgers : ∀ h, 0 < h →
      Secondary.actualLedger (DepthTree.midpoint 0 h (Nat.zero_le h)) (fun _ => true)
        allRight [List.replicate (h-1) true] = 1 := by
    intro h
    cases h with
    | zero => omega
    | succ h =>
      intro _
      simpa only [Nat.add_sub_cancel] using penultimate_secondary_ledger h
        (DepthTree.midpoint 0 (h+1) (Nat.zero_le _))
  have ledger : Secondary.actualLedger (DepthTree.midpoint 0 height (Nat.zero_le height))
      (fun _ => true) allRight [address] = 1 := by
    exact allLedgers height (by omega)
  have partition := leaf_toggle_forest allRight reference address pivot path.referenceAt
  rw [finalState] at partition nextInventory
  have cardinality : reference.size = 2^height-1 := by
    have count : reference.size+1 = 2^height := perfect_size height pivot
    omega
  refine ⟨reference,marked.erase,main.erase,trees,next,address,pivot,cost,work,rfl,cardinality,
    beforeOrdered,physicalWord,(SearchRotationBridge.rotations_inorder switch.rotations).trans physicalWord,
    inventory,nextInventory,history,access,by dsimp [cost]; omega,globalGain,
    right_ancestors _,actualWord,partition,ledger⟩

end MultiSplay.Obstructions.Classical
