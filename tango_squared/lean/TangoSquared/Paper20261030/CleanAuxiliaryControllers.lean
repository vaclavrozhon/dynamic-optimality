import TangoSquared.Paper20261030.AuxiliaryPayloadMap
import TangoSquared.Paper20261030.MarkedCut
import TangoSquared.Paper20261030.MarkedInsertion

/-! The local auxiliary controllers act on the existing clean components.
The payload-map identities identify their exact outputs with the split
and insertion definitions used by the maintained representation proofs.
No replacement representation or compatibility hypothesis is introduced. -/

namespace TangoSquared.Paper20261030.BoundaryObservations.CleanController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent SourceLocalProgram
open GapSource.Controller

variable {α κ ρ : Type*} [Ord κ]

theorem split [LawfulEqOrd κ] (component : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (key : κ) (found : searchResult key component.core = true) (outside) :
    ∃ reads cost, Run (code (SplitController.program key)) (.ready (.search 0))
      ⟨component.tree,outside⟩ (.ready (.returning 0))
      ⟨.fork (component.core.size,⟨key,(splitAt key component.core component.balanced found).value⟩)
        (cutLeft component key found).tree (cutRight component key found).tree,outside⟩ reads cost ∧
      cost ≤ 40110*Nat.clog 2 (component.core.size+1) := by
  let raw := component.core.map (fun _ value => value.1)
  have rawBalanced : raw.Balanced := PayloadMap.balanced _ component.balanced
  have rawFound : searchResult key raw = true := by simpa only [raw,PayloadMap.search_map] using found
  have ports : ∀ i, 0 ≤ i → i ≤ 0+(recordTree raw).size → boundary (component.ports i).rootRecord = true := by
    intro i _ bound
    apply marked i
    simpa only [Nat.zero_add,recordTree_size_of_balanced raw rawBalanced,raw,size_map] using bound
  obtain ⟨reads,cost,run,bound⟩ := SourceController.split key raw rawBalanced rawFound component.ports 0 ports outside
  rw [PayloadMap.clean_source component clean] at run
  have restored : (splitAt key raw rawBalanced rawFound).impl.map (fun _ value => (value,false)) =
      (splitAt key component.core component.balanced found).impl := by
    rw [PayloadMap.split_impl_map]
    simp only [raw,PayloadMap.clean_restore component.core clean]
  rw [PayloadMap.tree_as_map,restored,cut_exposed_tree] at run
  exact ⟨reads,cost,run,by simpa only [raw,size_map] using bound⟩

theorem join (old : Nat) (key : κ) (value : ρ×Bool) (unmarked : value.2 = false)
    (left right : Impl κ (fun _ => ρ×Bool)) (leftClean : Clean left) (rightClean : Clean right)
    (leftBalanced : left.Balanced) (rightBalanced : right.Balanced)
    (ports : Nat → Source α (MarkedRecord κ ρ))
    (marked : ∀ i, i ≤ left.size+1+right.size → boundary (ports i).rootRecord = true) (outside) :
    ∃ reads cost, Run (code JoinController.program) (.ready (.observing 0 (.read 3 [])))
      ⟨GapSource.encode (recordTree (.inner old key value left right)) ports 0,outside⟩ (.ready (.returning 0))
      ⟨GapSource.encode (recordTree (link key value left right leftBalanced rightBalanced).impl) ports 0,outside⟩ reads cost ∧
      cost ≤ 2100*(Nat.clog 2 (left.size+1)+Nat.clog 2 (right.size+1))+308 := by
  let rawLeft := left.map (fun _ value => value.1)
  let rawRight := right.map (fun _ value => value.1)
  have hl : rawLeft.Balanced := PayloadMap.balanced _ leftBalanced
  have hr : rawRight.Balanced := PayloadMap.balanced _ rightBalanced
  have portsMarked : ∀ i, 0 ≤ i → i ≤ 0+(recordTree (.inner old key value.1 rawLeft rawRight)).size →
      boundary (ports i).rootRecord = true := by
    intro i _ bound
    apply marked i
    simpa only [recordTree,MTR.Tree.size,Nat.zero_add,recordTree_size_of_balanced rawLeft hl,
      recordTree_size_of_balanced rawRight hr,rawLeft,rawRight,size_map] using bound
  obtain ⟨reads,cost,run,bound⟩ := SourceController.join old key value.1 rawLeft rawRight hl hr ports 0 portsMarked outside
  have valueRestored : (value.1,false) = value := Prod.ext rfl unmarked.symm
  simp only [PayloadMap.tree_as_map,PayloadMap.link_map,Impl.map,rawLeft,rawRight,
    PayloadMap.clean_restore left leftClean,PayloadMap.clean_restore right rightClean,valueRestored] at run
  simp only [link_eq_link!,PayloadMap.clean_restore left leftClean,PayloadMap.clean_restore right rightClean] at run
  exact ⟨reads,cost,by simpa only [link_eq_link!] using run,
    by simpa only [rawLeft,rawRight,size_map] using bound⟩

theorem append (component : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (key : κ) (value : ρ×Bool) (unmarked : value.2 = false)
    (sibling : Source α (MarkedRecord κ ρ)) (siblingMarked : entry sibling.rootRecord = true)
    (old : Nat) (outside) :
    ∃ reads cost, Run (code JoinController.program) (.ready (.observing 0 (.read 3 [])))
      ⟨.fork (old,⟨key,value⟩) component.tree sibling,outside⟩ (.ready (.returning 0))
      ⟨(AuxiliaryComponent.append component key value sibling).tree,outside⟩ reads cost ∧
      cost ≤ 2100*Nat.clog 2 (component.core.size+1)+308 := by
  have ports := marked_append component marked key value sibling siblingMarked
  obtain ⟨reads,cost,run,bound⟩ := join old key value unmarked component.core .leaf clean True.intro
    component.balanced .leaf (AuxiliaryComponent.append component key value sibling).ports
    (by intro i hi; apply ports i; rw [append_size]; simpa only [Impl.size_leaf,Nat.add_zero] using hi) outside
  rw [append_input] at run
  have target (tree : Impl κ (fun _ => ρ×Bool)) (balanced : tree.Balanced) :
      (link key value tree .leaf balanced .leaf).impl = (insertMax key value tree balanced).impl := by
    cases tree <;> simp only [link,insertMin,insertMax]
  rw [target component.core component.balanced] at run
  exact ⟨reads,cost,run,by simpa only [Impl.size_leaf,Nat.zero_add,Nat.clog_one_right,Nat.add_zero] using bound⟩

theorem prepend (component : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (key : κ) (value : ρ×Bool) (unmarked : value.2 = false)
    (sibling : Source α (MarkedRecord κ ρ)) (siblingMarked : entry sibling.rootRecord = true)
    (old : Nat) (outside) :
    ∃ reads cost, Run (code JoinController.program) (.ready (.observing 0 (.read 3 [])))
      ⟨.fork (old,⟨key,value⟩) sibling component.tree,outside⟩ (.ready (.returning 0))
      ⟨(AuxiliaryComponent.prepend key value sibling component).tree,outside⟩ reads cost ∧
      cost ≤ 2100*Nat.clog 2 (component.core.size+1)+308 := by
  have ports := marked_prepend key value sibling siblingMarked component marked
  obtain ⟨reads,cost,run,bound⟩ := join old key value unmarked .leaf component.core True.intro clean
    .leaf component.balanced (AuxiliaryComponent.prepend key value sibling component).ports
    (by intro i hi; apply ports i; rw [prepend_size]; simpa only [Impl.size_leaf,Nat.zero_add,Nat.add_comm] using hi) outside
  rw [prepend_input,link] at run
  exact ⟨reads,cost,run,by simpa only [Impl.size_leaf,Nat.zero_add,Nat.clog_one_right] using bound⟩

end TangoSquared.Paper20261030.BoundaryObservations.CleanController
