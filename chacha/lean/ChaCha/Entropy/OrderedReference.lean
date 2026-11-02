import ChaCha.Paper20261030.PrimaryRectangleBound

/-!
# Alternations in an arbitrary ordered auxiliary reference

The reference may be chosen after seeing the request word. Its leaves
are the original ordered keys, and its counter is the existing Wilber
primary counter. Convex splitting charges that actual counter to the
same robust rectangle bound used by Cha-Cha.
-/

namespace ChaCha.Entropy

open PreferredProjection Paper20261030 Paper20261030.Dyadic Paper20261030.Rectangles Secondary

def firstKey : PrefRouter Int → Int
  | .leaf key => key
  | .fork _ left _ => firstKey left

theorem firstKey_mem (reference : PrefRouter Int) : firstKey reference ∈ reference.leaves := by
  induction reference with
  | leaf => simp [firstKey,PrefRouter.leaves]
  | fork _ left right ihl _ => simp only [firstKey,PrefRouter.leaves,List.mem_append]; exact Or.inl ihl

theorem firstKey_le (reference : PrefRouter Int) (ordered : reference.leaves.Pairwise (· < ·)) :
    ∀ key ∈ reference.leaves, firstKey reference ≤ key := by
  induction reference with
  | leaf root =>
      intro key member
      have same : key = root := List.mem_singleton.mp member
      subst key
      exact le_rfl
  | fork _ left right ihl _ =>
      have parts := List.pairwise_append.mp ordered
      intro key member
      rcases List.mem_append.mp member with low | high
      · exact ihl parts.1 key low
      · exact le_of_lt (parts.2.2 _ (firstKey_mem left) key high)

theorem ordered_primary_robust (reference : PrefRouter Int)
    (ordered : reference.leaves.Pairwise (· < ·)) (points : List Point)
    (chronological : Chronological points) (keys : ∀ point ∈ points, point.1 ∈ reference.leaves) :
    reference.primaryWilber (points.map Prod.fst) ≤ robustBound points.toFinset := by
  induction reference generalizing points with
  | leaf key => simp only [PrefRouter.primaryWilber]; exact Nat.zero_le _
  | fork preference left right ihl ihr =>
      have parts := List.pairwise_append.mp ordered
      let cut := firstKey right
      let projection : Int → Int := fun key => if key < cut then 0 else 1
      have lower : ∀ key ∈ left.leaves, key < cut :=
        fun key present => parts.2.2 key present cut (firstKey_mem right)
      have upper : ∀ key ∈ right.leaves, cut ≤ key := firstKey_le right parts.2.1
      have leftClass : ∀ key ∈ left.leaves ++ right.leaves,
          key ∈ left.leaves ↔ projection key = 0 := by
        intro key member
        constructor
        · intro present
          simp only [projection,if_pos (lower key present)]
        · intro zero
          rcases List.mem_append.mp member with present | present
          · exact present
          · simp only [projection,if_neg (not_lt_of_ge (upper key present))] at zero
            omega
      have rightClass : ∀ key ∈ left.leaves ++ right.leaves,
          (key ∉ left.leaves ∧ key ∈ right.leaves) ↔ projection key = 1 := by
        intro key member
        have classified := leftClass key member
        constructor
        · rintro ⟨notLeft,present⟩
          simp only [projection,if_neg (not_lt_of_ge (upper key present))]
        · intro one
          have notLeft : key ∉ left.leaves := by intro present; have zero := classified.mp present; omega
          exact ⟨notLeft,(List.mem_append.mp member).resolve_left notLeft⟩
      let low := points.filter (fun point => decide (point.1 ∈ left.leaves))
      let high := points.filter (fun point => decide (point.1 ∉ left.leaves ∧ point.1 ∈ right.leaves))
      have lowKeys : ∀ point ∈ low, point.1 ∈ left.leaves := by
        intro point member
        exact of_decide_eq_true (List.mem_filter.mp member).2
      have highKeys : ∀ point ∈ high, point.1 ∈ right.leaves := by
        intro point member
        exact (of_decide_eq_true (List.mem_filter.mp member).2).2
      have lowBound := ihl parts.1 low (chronological_filter chronological _) lowKeys
      have highBound := ihr parts.2.1 high (chronological_filter chronological _) highKeys
      have lowWord : low.map Prod.fst = PrefRouter.leftWord left.leaves (points.map Prod.fst) :=
        keys_filter_points points (fun key => decide (key ∈ left.leaves))
      have highWord : high.map Prod.fst = PrefRouter.rightWord left.leaves right.leaves (points.map Prod.fst) :=
        keys_filter_points points (fun key => decide (key ∉ left.leaves ∧ key ∈ right.leaves))
      have lowSet : low.toFinset = fiber projection 0 points.toFinset := by
        ext point
        simp only [low,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,fiber,Finset.mem_filter]
        exact and_congr_right (fun present => leftClass point.1 (keys point present))
      have highSet : high.toFinset = fiber projection 1 points.toFinset := by
        ext point
        simp only [high,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,fiber,Finset.mem_filter]
        exact and_congr_right (fun present => rightClass point.1 (keys point present))
      have branchWord :
          (PrefRouter.branchWord left.leaves right.leaves (points.map Prod.fst)).map (branchIndex 0) =
            (points.map Prod.fst).map projection := by
        have allKeys : ∀ key ∈ points.map Prod.fst, key ∈ left.leaves ++ right.leaves := by
          intro key member
          obtain ⟨point,present,rfl⟩ := List.mem_map.mp member
          exact keys point present
        generalize points.map Prod.fst = word at allKeys ⊢
        induction word with
        | nil => rfl
        | cons key word ih =>
            have valid := allKeys key (by simp)
            have rest := ih (fun other present => allKeys other (by simp [present]))
            by_cases inLeft : key ∈ left.leaves
            · have zero := (leftClass key valid).mp inLeft
              simp [PrefRouter.branchWord,inLeft,branchIndex,zero]
              exact rest
            · have inRight := (List.mem_append.mp valid).resolve_left inLeft
              have one := (rightClass key valid).mp ⟨inLeft,inRight⟩
              simp [PrefRouter.branchWord,inLeft,inRight,branchIndex,one]
              exact rest
      have switches := alternations_switchCount (points.map (mapPoint projection))
        (chronological_project chronological projection)
      have projected : (points.map (mapPoint projection)).toFinset = project projection points.toFinset := by
        ext point
        simp [project]
      have pointKeys : (points.map (mapPoint projection)).map Prod.fst =
          (points.map Prod.fst).map projection := by simp only [List.map_map]; rfl
      rw [projected,pointKeys,← branchWord,alternations_injective_map _ (branchIndex_injective 0)] at switches
      have switchBound := switchCount_le_robustBound (instance_project (chronological_instance chronological) projection)
      have monotone : Monotone projection := by
        intro x y below
        dsimp only [projection]
        split_ifs <;> omega
      have split := robustBound_split (chronological_instance chronological) projection monotone {0,1}
      rw [Finset.sum_pair (by decide : (0:Int) ≠ 1)] at split
      rw [lowSet] at lowBound
      rw [highSet] at highBound
      simp only [PrefRouter.primaryWilber]
      rw [← lowWord,← highWord]
      change alternations (PrefRouter.branchWord left.leaves right.leaves (points.map Prod.fst)) = _ at switches
      omega

theorem ordered_reference_robust (reference : PrefRouter Int)
    (ordered : reference.leaves.Pairwise (· < ·)) (requests : List Int)
    (keys : ∀ key ∈ requests, key ∈ reference.leaves) :
    reference.primaryWilber requests ≤ robustBound (accessPoints requests) := by
  have pointKeys : ∀ point ∈ pointWord 0 requests, point.1 ∈ reference.leaves := by
    intro point member
    have present : point.1 ∈ (pointWord 0 requests).map Prod.fst := List.mem_map.mpr ⟨point,member,rfl⟩
    rw [pointWord_keys] at present
    exact keys point.1 present
  have bound := ordered_primary_robust reference ordered (pointWord 0 requests)
    (pointWord_chronological 0 requests) pointKeys
  simpa only [pointWord_keys,pointWord_toFinset] using bound

end ChaCha.Entropy
