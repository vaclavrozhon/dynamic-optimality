import ChaCha.Separation.NumericPrimary
import ChaCha.Paper20261030.RectangleSplit

/-!
# Robust certificates survive increasing embeddings of active ranks

The finite rank map is nondecreasing on the entire integer universe,
including values between active keys. Thus the existing robust splitting
theorem applies to the actual original access points and timestamps.
-/

namespace ChaCha.Separation

open Paper20261030 Paper20261030.Rectangles

def rankProjection (embedding : Nat → Int) (count : Nat) (value : Int) : Int :=
  (((Finset.range count).filter (fun index => embedding index ≤ value)).card : Int)-1

theorem rankProjection_monotone (embedding : Nat → Int) (count : Nat) :
    Monotone (rankProjection embedding count) := by
  intro x y ordered
  have inclusion : (Finset.range count).filter (fun index => embedding index ≤ x) ⊆
      (Finset.range count).filter (fun index => embedding index ≤ y) := by
    intro index member
    obtain ⟨present,before⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨present,before.trans ordered⟩
  have cardinality := Finset.card_le_card inclusion
  unfold rankProjection
  omega

theorem rankProjection_embedding (embedding : Nat → Int) (increasing : StrictMono embedding)
    {count index : Nat} (valid : index < count) :
    rankProjection embedding count (embedding index) = (index : Int) := by
  have selected : (Finset.range count).filter (fun other => embedding other ≤ embedding index) =
      Finset.range (index+1) := by
    ext other
    simp only [Finset.mem_filter,Finset.mem_range,increasing.le_iff_le]
    omega
  simp only [rankProjection,selected,Finset.card_range,Nat.cast_add,Nat.cast_one]
  omega

theorem pointWord_map (f : Int → Int) (start : Int) (requests : List Int) :
    pointWord start (requests.map f) = (pointWord start requests).map (mapPoint f) := by
  induction requests generalizing start with
  | nil => rfl
  | cons request requests ih => simp only [List.map_cons,pointWord,ih,mapPoint]

theorem project_accessPoints (f : Int → Int) (requests : List Int) :
    project f (accessPoints requests) = accessPoints (requests.map f) := by
  have same := congrArg List.toFinset (pointWord_map f 0 requests)
  have mapped : ((pointWord 0 requests).map (mapPoint f)).toFinset =
      project f (pointWord 0 requests).toFinset := by
    ext point
    simp only [project,List.mem_toFinset,List.mem_map,Finset.mem_image]
  rw [pointWord_toFinset,mapped,pointWord_toFinset] at same
  exact same.symm

theorem robust_map_le (f : Int → Int) (monotone : Monotone f) (requests : List Int) :
    robustBound (accessPoints (requests.map f)) ≤ robustBound (accessPoints requests) := by
  have bound := robustBound_split (accessPoints_instance requests) f monotone ∅
  simpa only [Finset.sum_empty,Nat.add_zero,project_accessPoints] using bound

/-- Only the projection must be monotone on the entire universe. The
embedding needs a left inverse on the keys that actually occur. -/
theorem robust_embedding (requests : List Int) (embedding projection : Int → Int)
    (monotone : Monotone projection)
    (inverse : ∀ key ∈ requests, projection (embedding key) = key) :
    robustBound (accessPoints requests) ≤ robustBound (accessPoints (requests.map embedding)) := by
  have recovered : (requests.map embedding).map projection = requests := by
    rw [List.map_map]
    calc
      _ = requests.map id := List.map_congr_left (fun key member => inverse key member)
      _ = requests := List.map_id requests
  have lower := robust_map_le projection monotone (requests.map embedding)
  rwa [recovered] at lower

theorem robust_increasing_embedding (embedding : Nat → Int) (increasing : StrictMono embedding)
    (count : Nat) (requests : List Nat) (valid : ∀ key ∈ requests, key < count) :
    robustBound (accessPoints (requests.map (fun key : Nat => (key : Int)))) ≤
      robustBound (accessPoints (requests.map embedding)) := by
  have recovered : (requests.map embedding).map (rankProjection embedding count) =
      requests.map (fun key : Nat => (key : Int)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro key member
    exact rankProjection_embedding embedding increasing (valid key member)
  have lower := robust_map_le (rankProjection embedding count)
    (rankProjection_monotone embedding count) (requests.map embedding)
  rwa [recovered] at lower

theorem robust_increasing_embedding_eq (embedding : Nat → Int) (increasing : StrictMono embedding)
    (count : Nat) (requests : List Nat) (valid : ∀ key ∈ requests, key < count) :
    robustBound (accessPoints (requests.map embedding)) =
      robustBound (accessPoints (requests.map (fun key : Nat => (key : Int)))) := by
  apply Nat.le_antisymm
  · let extended : Int → Int := fun key => embedding key.toNat
    have monotone : Monotone extended := fun x y ordered =>
      increasing.monotone (Int.toNat_le_toNat ordered)
    have same : (requests.map (fun key : Nat => (key : Int))).map extended =
        requests.map embedding := by
      simp only [List.map_map,Function.comp_def,extended,Int.toNat_natCast]
    have upper := robust_map_le extended monotone (requests.map (fun key : Nat => (key : Int)))
    rwa [same] at upper
  · exact robust_increasing_embedding embedding increasing count requests valid

end ChaCha.Separation
