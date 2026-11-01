import LabelTimeline

/-!
Lift a local atom-index update timeline to actual persistent records.
Only injectivity on the finite active atom domain is required, rather
than an impossible global injection from Nat to a finite record type.
-/
namespace GreedyForest.Timeline

variable {LocalRecord GlobalRecord Block : Type*}
  [DecidableEq LocalRecord] [DecidableEq GlobalRecord]

def Update.mapRecord (f : LocalRecord → GlobalRecord) (u : Update LocalRecord Block) :
    Update GlobalRecord Block where
  record := f u.record
  value := u.value
  origin := u.origin
  good := u.good

theorem mapped_apply_on_domain (domain : Finset LocalRecord) (f : LocalRecord → GlobalRecord)
    (hinj : Set.InjOn f (domain : Set LocalRecord))
    (localLabels : LocalRecord → ℤ) (globalLabels : GlobalRecord → ℤ)
    (hlabels : ∀ v ∈ domain, globalLabels (f v)=localLabels v)
    (u : Update LocalRecord Block) (hu : u.record ∈ domain) :
    ∀ v ∈ domain,
      applyUpdate globalLabels (u.mapRecord f) (f v) = applyUpdate localLabels u v := by
  intro v hv
  by_cases heq : v=u.record
  · subst v; simp [applyUpdate,Update.mapRecord]
  · have hne : f v ≠ f u.record := by
      intro h; exact heq (hinj hv hu h)
    simpa only [applyUpdate,Update.mapRecord,Function.update_of_ne hne,
      Function.update_of_ne heq] using hlabels v hv

/-- Local validity transfers using the actual initial snapshot values
on the finite atom domain. The mapped updates need no new certificates. -/
theorem valid_map_records {K : ℤ} (domain : Finset LocalRecord) (f : LocalRecord → GlobalRecord)
    (hinj : Set.InjOn f (domain : Set LocalRecord))
    (localLabels : LocalRecord → ℤ) (globalLabels : GlobalRecord → ℤ)
    (hlabels : ∀ v ∈ domain, globalLabels (f v)=localLabels v)
    (updates : List (Update LocalRecord Block))
    (hinside : ∀ u ∈ updates, u.record ∈ domain) (hvalid : Valid K localLabels updates) :
    Valid K globalLabels (updates.map (Update.mapRecord f)) := by
  induction updates generalizing localLabels globalLabels with
  | nil => trivial
  | cons u rest ih =>
      have hu := hinside u (by simp)
      refine ⟨⟨hvalid.1.1,?_,?_⟩,?_⟩
      · intro hfree
        have h := hvalid.1.2.1 hfree
        change u.value ≤ globalLabels (f u.record)
        rw [hlabels u.record hu]
        exact h
      · intro hgood
        have h := hvalid.1.2.2 hgood
        change u.value+1 ≤ globalLabels (f u.record)
        rw [hlabels u.record hu]
        exact h
      · apply ih (applyUpdate localLabels u) (applyUpdate globalLabels (u.mapRecord f))
          (mapped_apply_on_domain domain f hinj localLabels globalLabels hlabels u hu)
          (fun v hv => hinside v (by simp [hv])) hvalid.2

theorem mapped_run_on_domain (domain : Finset LocalRecord) (f : LocalRecord → GlobalRecord)
    (hinj : Set.InjOn f (domain : Set LocalRecord))
    (localLabels : LocalRecord → ℤ) (globalLabels : GlobalRecord → ℤ)
    (hlabels : ∀ v ∈ domain, globalLabels (f v)=localLabels v)
    (updates : List (Update LocalRecord Block))
    (hinside : ∀ u ∈ updates, u.record ∈ domain) :
    ∀ v ∈ domain, run globalLabels (updates.map (Update.mapRecord f)) (f v) =
      run localLabels updates v := by
  induction updates generalizing localLabels globalLabels with
  | nil => exact hlabels
  | cons u rest ih =>
      exact ih (applyUpdate localLabels u) (applyUpdate globalLabels (u.mapRecord f))
        (mapped_apply_on_domain domain f hinj localLabels globalLabels hlabels u (hinside u (by simp)))
        (fun v hv => hinside v (by simp [hv]))

/-- Every local phase snapshot, including pre-update entry snapshots,
is preserved by the actual record embedding. -/
theorem mapped_snapshot_on_domain (domain : Finset LocalRecord) (f : LocalRecord → GlobalRecord)
    (hinj : Set.InjOn f (domain : Set LocalRecord))
    (localLabels : LocalRecord → ℤ) (globalLabels : GlobalRecord → ℤ)
    (hlabels : ∀ v ∈ domain, globalLabels (f v)=localLabels v)
    (updates : List (Update LocalRecord Block))
    (hinside : ∀ u ∈ updates, u.record ∈ domain) (time : ℕ) :
    ∀ v ∈ domain, stateAt globalLabels (updates.map (Update.mapRecord f)) time (f v) =
      stateAt localLabels updates time v := by
  simp only [stateAt,←List.map_take]
  apply mapped_run_on_domain domain f hinj localLabels globalLabels hlabels (updates.take time)
  intro u hu
  exact hinside u (List.mem_of_mem_take hu)

end GreedyForest.Timeline

#print axioms GreedyForest.Timeline.valid_map_records
#print axioms GreedyForest.Timeline.mapped_snapshot_on_domain
