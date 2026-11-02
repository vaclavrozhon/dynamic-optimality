import DynamicOptimality.ColoredWalks.ShuffleWalk
import DynamicOptimality.ColoredWalks.ShuffleEncoding
import DynamicOptimality.ColoredWalks.ShuffleArithmetic
import DynamicOptimality.ColoredWalks.ProjectionExecution
import DynamicOptimality.GeometricCost
import DynamicOptimality.ModelInitialization

/-! # From literal colored walks to the shared optimum

The reduction first builds the static colored tree on exactly the observed
colored keys, executes the persistent fingers, and invokes the single-tree
simulation. A monotone geometric projection merges colored copies and omits
unused original keys. Thus the optimum bound has no universe-size startup
term. A supplied initial BST is handled by the existing initialization lemma.

This module states the reduction with an explicit `SimulationBound` premise.
The public shuffle endpoint instantiates that premise with the actual
persistent-hand simulation; the premise is not itself a new axiom.
-/

namespace DynamicOptimality.ColoredWalks

open ChaCha.MTR MultiFinger

variable {n k : Nat} {events : List (Fin k × Fin n)}

theorem encoded_search_bound {constant : Nat} (simulation : SimulationBound constant)
    (encoding : Encoding events) (sets : Fin k → Finset (Fin n))
    (walk : ShuffleWalk sets events) :
    ∃ cost, ModelCosts.search (events.map encoding.encode) cost ∧
      cost ≤ 11*constant*events.length*(logarithmicFactor k)^2 := by
  obtain ⟨tree,embedding⟩ := exists_colored_embedding encoding.natLabel
    (List.range encoding.size) List.pairwise_lt_range
  have ordered : tree.Ordered := by
    change tree.inorder.Pairwise (· < ·)
    rw [embedding.word]
    exact List.pairwise_lt_range
  have treeSize : tree.size = encoding.size := by
    rw [← Tree.length_inorder,embedding.word,List.length_range]
  obtain ⟨positions,bounded,short⟩ := encoding.shuffle_short_walk sets walk embedding
  have present : ∀ index, positions index ∈ tree.inorder := by
    intro index
    rw [embedding.word]
    exact List.mem_range.mpr (bounded index)
  obtain ⟨initial,initialAt⟩ := configuration_exists positions present
  have live : initial.Live := by
    intro index empty
    have key := initialAt index
    rw [empty] at key
    cases key
  obtain ⟨final,fingerCost,fingerRun,fingerBound⟩ := short.execute ordered initial initialAt
  have fingerCharge : fingerCost ≤ events.length*(4*Nat.clog 2 (2*encoding.count+1)+1) := by
    simpa only [Encoding.encodedEvents,List.length_map] using fingerBound
  obtain ⟨before,after,cost,beforeOrdered,beforeWord,actual,charge⟩ :=
    simulation tree encoding.count initial final _ fingerCost ordered encoding.count_pos live fingerRun
  have word : before.inorder = List.range encoding.size := beforeWord.trans embedding.word
  obtain ⟨indexed,indexedEq⟩ := OnlineModel.indexed_of_inorder before word
  have search : ModelCosts.search (events.map encoding.encode) cost := by
    refine ⟨indexed,after,?_⟩
    rw [indexedEq]
    simpa only [Encoding.encodedEvents,List.map_map,Function.comp_def] using actual
  have arithmetic := shuffle_budget encoding.size_le_length encoding.count_le_length
    encoding.count_le_colors fingerCharge
  rw [treeSize] at charge
  refine ⟨cost,search,charge.trans ?_⟩
  have scaled := Nat.mul_le_mul_left constant arithmetic
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using scaled

theorem shuffle_OPT_of_simulation {constant : Nat} (simulation : SimulationBound constant)
    (sets : Fin k → Finset (Fin n)) (walk : ShuffleWalk sets events) :
    OPT (events.map Prod.snd) ≤ 286*constant*events.length*(logarithmicFactor k)^2 := by
  by_cases empty : events = []
  · subst events
    simp [OPT]
  · let encoding := observedEncoding events empty
    obtain ⟨cost,search,charge⟩ := encoded_search_bound simulation encoding sets walk
    have optimal : OPT (events.map encoding.encode) ≤ 2*cost :=
      ModelCosts.searchComparison.lower _ search
    obtain ⟨geometricCost,geometry,geometryCharge⟩ :=
      ModelCosts.geometry_upper (events.map encoding.encode)
    obtain ⟨projectedCost,projectionCharge,projected⟩ := Geometry.execution_map_monotone
      (fun rank => (encoding.decode rank).2) encoding.monotone_key
      (events.map encoding.encode) geometry
    have decoded : (events.map encoding.encode).map (fun rank => (encoding.decode rank).2) =
        events.map Prod.snd := by
      rw [List.map_map]
      apply List.map_congr_left
      intro event member
      exact congrArg Prod.snd (encoding.decode_encode event member)
    rw [decoded] at projected
    have original : OPT (events.map Prod.snd) ≤ 13*projectedCost :=
      ModelCosts.geometryComparison.lower _ projected
    nlinarith

theorem shuffle_from_initial_of_simulation {constant : Nat} (simulation : SimulationBound constant)
    (sets : Fin k → Finset (Fin n)) (walk : ShuffleWalk sets events) (initial : BST 0 n) :
    ∃ (final : BST 0 n) (cost : Nat),
      SearchRotation.Execution initial.toRaw ((events.map Prod.snd).map Fin.val) final.toRaw cost ∧
      cost ≤ 572*constant*events.length*(logarithmicFactor k)^2+12*n := by
  obtain ⟨final,cost,run,bound⟩ := ModelInitialization.search_from_initial initial (events.map Prod.snd)
  have optimal := shuffle_OPT_of_simulation simulation sets walk
  exact ⟨final,cost,run,by nlinarith⟩

end DynamicOptimality.ColoredWalks
