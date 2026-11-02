import MultiSplay.InitializedOnline
import MultiSplay.CompetitiveFactor
import MultiSplay.ForestProgram

/-! # The exact-word comparator interface

The comparator must execute the actual classical switch history from the
same component domains. Its budget is an explicit premise of the numerical
reductions; `Online.comparator_estimate` later constructs this witness.
Keeping the interface here lets generic and concrete factors share one
initialization argument without an import cycle.
-/

namespace MultiSplay.Online

open DynamicOptimality
open CommonForest ClassicalSwitch EndpointEncoding

def ComparatorEstimate (scale : Nat) : Prop :=
  ∀ n (requests : List (Fin n)),
    ∃ sources targets budget,
      domains sources = domains (forest (fun _ => true) (balancedReference n).toRaw) ∧
      Program sources
        (historyWord (balancedReference n).toRaw (fun _ => true)
          (requests.map fun key => nodeAddress (balancedReference n) key.val)) targets budget ∧
      budget ≤ scale * comparisonFactor (balancedReference n).height * (OPT requests+n)

end MultiSplay.Online
