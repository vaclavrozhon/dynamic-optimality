import MultiSplay.ComparatorForestInvariant
import MultiSplay.ComparatorProgramChronology
import MultiSplay.ComparatorStableTransaction
import MultiSplay.InitializedComparatorBound

/-! # From a maintained local comparator to the shared optimum

The only construction supplied to this reduction is the actual one-switch
service. Initialization, chronological composition, row-variation charging,
the exact-key reference, and the final physical cost reduction are proved
here or in the imported modules.
-/

namespace MultiSplay.ComparatorForest

open DynamicOptimality (RawTree BST OPT Competitive)
open ChaCha
open EndpointEncoding ClassicalSwitch CommonForest

theorem comparator_estimate_of_services (scale : Nat)
    (services : ∀ n, ComparatorHistory.Service (balancedHierarchy n) (balancedReference n).toRaw
      (scale * ComparatorStableSuffix.seamFactor (balancedHierarchy n))
      (Maintained (balancedReference n) (balancedHierarchy n))) :
    Online.ComparatorEstimate (scale * 2137120) := by
  intro n requests
  let state : State := fun _ => true
  let memory : Memory := fun _ => true
  let addresses := requests.map fun key => nodeAddress (balancedReference n) key.val
  let family := initialFamily (balancedHierarchy n) state memory
  let sources := projectedForest state (balancedReference n) family
  have valid : Maintained (balancedReference n) (balancedHierarchy n) state memory sources :=
    ⟨family,initial_valid state (balancedReference n) (balancedHierarchy n) memory,rfl⟩
  have real : ∀ address ∈ addresses, referenceAt (balancedReference n).toRaw address ≠ .empty := by
    intro address member
    obtain ⟨key,_,rfl⟩ := List.mem_map.mp member
    obtain ⟨left,right,found⟩ := referenceAt_nodeAddress (balancedReference n) (Nat.zero_le key.val) key.isLt
    simp [found]
  obtain ⟨targets,budget,program,paid⟩ := ComparatorHistory.service_history_le_actual
    (balancedHierarchy n) (balancedReference n).toRaw
    (scale * ComparatorStableSuffix.seamFactor (balancedHierarchy n))
    (Maintained (balancedReference n) (balancedHierarchy n)) (services n)
    state memory sources addresses valid real
  have counters := balancedReference_counters_le_OPT requests (balancedHierarchy n) state
  simp only [List.map_map,Function.comp_def] at counters
  have counterBound : (actualHistory state addresses).length +
      Secondary.actualLedger (balancedHierarchy n) memory state addresses ≤ 2137120*(OPT requests+n) := by
    change requests.length + (actualHistory state addresses).length +
      Secondary.actualLedger (balancedHierarchy n) memory state addresses ≤
      2137120*(OPT requests+n) at counters
    omega
  have hierarchy : ComparatorStableSuffix.seamFactor (balancedHierarchy n) ≤
      comparisonFactor (balancedReference n).height := balancedHierarchy_repairFactor_le n
  refine ⟨sources,targets,budget,initial_domains state (balancedReference n) (balancedHierarchy n) memory,program,?_⟩
  calc
    budget ≤ (scale * ComparatorStableSuffix.seamFactor (balancedHierarchy n)) *
        ((actualHistory state addresses).length + Secondary.actualLedger (balancedHierarchy n) memory state addresses) := paid
    _ ≤ (scale * comparisonFactor (balancedReference n).height) * (2137120*(OPT requests+n)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left scale hierarchy) counterBound
    _ = (scale*2137120)*comparisonFactor (balancedReference n).height*(OPT requests+n) := by ring

theorem competitive_of_services (scale : Nat)
    (services : ∀ n, ComparatorHistory.Service (balancedHierarchy n) (balancedReference n).toRaw
      (scale * ComparatorStableSuffix.seamFactor (balancedHierarchy n))
      (Maintained (balancedReference n) (balancedHierarchy n))) :
    Competitive Online.cost shiftedEGFactor :=
  Online.competitive_of_comparator_estimate (comparator_estimate_of_services scale services)

end MultiSplay.ComparatorForest
