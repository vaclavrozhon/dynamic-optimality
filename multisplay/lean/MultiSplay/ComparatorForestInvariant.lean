import MultiSplay.ComparatorForestMemory

/-! The maintained projected comparator forest, without the final cost imports. -/

namespace MultiSplay.ComparatorForest

open DynamicOptimality (RawTree BST)
open ChaCha
open EndpointEncoding

def Maintained {lower upper : Nat} (reference : BST lower upper)
    (secondary : DepthTree 0 reference.height) (state : State) (memory : Memory)
    (trees : List (RawTree Nat)) : Prop :=
  ∃ family : Family, family.Valid secondary state reference memory ∧
    trees = projectedForest state reference family

end MultiSplay.ComparatorForest
