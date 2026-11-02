import ChaCha.Paper20261030.AbstractBound

/-! Retaining the robust maximum already present in the manuscript's
potential gives a stronger form of the existing abstract work bound.
No events, preferences, or execution costs are redefined here. -/

namespace ChaCha.Paper20261030.Rectangles

theorem potential_le_robustBound (P : Finset Point) : potential P ≤ 5*(robustBound P : Int) := by
  unfold potential
  omega

theorem SplitDecomposition.alternations_le_robustBound {P : Finset Point}
    (decomposition : SplitDecomposition P) (valid : Instance P) :
    decomposition.alternations ≤ 5*robustBound P := by
  have telescopes := decomposition.telescope valid
  have leaves := decomposition.leafPotential_nonnegative valid
  have magnitude := potential_le_robustBound P
  omega

end ChaCha.Paper20261030.Rectangles

namespace ChaCha.Paper20261030.Dyadic

open Rectangles Secondary

theorem sequence_lcaBound_robust {h : Nat} (reference : DepthTree 0 h) (requests : List Int)
    (keys : ∀ key ∈ requests, ValidKey (h+1) key) :
    lcaBound (h+1) reference (accessPoints requests) ≤ 5*robustBound (accessPoints requests) := by
  have valid := accessPoints_instance requests
  rw [lcaBound_eq_fragmentAlternations reference valid (accessPoints_keys keys) (Nat.le_refl _),
    project_self,fragmentAlternations_eq_decomposition reference valid]
  exact (fragmentDecomposition reference _).alternations_le_robustBound valid

theorem primaryWilber_robust {height : Nat} (requests : List Int)
    (keys : ∀ key ∈ requests, ValidKey height key) :
    (canonical height 0).primaryWilber requests ≤ robustBound (accessPoints requests) := by
  have members : ∀ point ∈ pointWord 0 requests, point.1 ∈ (canonical height 0).leaves := by
    intro point member
    have keyMember : point.1 ∈ (pointWord 0 requests).map Prod.fst := List.mem_map.mpr ⟨point,member,rfl⟩
    rw [pointWord_keys] at keyMember
    exact (canonical_zero_mem _ _).mpr (keys point.1 keyMember)
  have count := primaryWilber_robustBound height 0 (pointWord 0 requests) (pointWord_chronological 0 requests) members
  simpa only [pointWord_keys,pointWord_toFinset] using count

theorem abstract_work_robust_bound {h : Nat} (reference : DepthTree 0 h) (requests : List Int)
    (keys : ∀ key ∈ requests, ValidKey (h+1) key) :
    abstractWork reference requests + 6 ≤
      requests.length+13*robustBound (accessPoints requests)+6*2^(h+1) := by
  have secondary := secondary_flip_bound reference (MemoryState.initial (canonical (h+1) 0))
    (canonical_perfect _ _) (canonical_nodup _ _) requests
    (fun key member => (canonical_zero_mem _ _).mpr (keys key member))
  have lca := sequence_lcaBound_robust reference requests keys
  rw [← memoryLCA_eq_lcaBound reference requests keys] at lca
  have primary := primaryWilber_robust requests keys
  have accesses := (canonical (h+1) 0).depth_access_bound requests
  have leaves := perfect_leaf_count (canonical_perfect (h+1) 0)
  have vertices := (canonical (h+1) 0).internal_vertices_leaves
  dsimp only [MemoryState.initial] at secondary
  unfold abstractWork MemoryState.initial
  omega

end ChaCha.Paper20261030.Dyadic
