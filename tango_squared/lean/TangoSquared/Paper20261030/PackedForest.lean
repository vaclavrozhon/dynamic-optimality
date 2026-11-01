import TangoSquared.Paper20261030.ProjectionForest

/-!
# Keeping all color cursors synchronized after every source operation

Each source step is performed in every projection before the next source
step begins. The existing one-cursor kernels serialize into actual forest
instructions with cost at most seventeen times the number of colors.
Source reads use only the owning color's reached vertex, whose bounded
record list contains the requested source record. Decoding a record's
identity and obtaining rotation inputs are separate local-control tasks.
-/

namespace TangoSquared.Paper20261030.ProjectionForest

open ColoredStorage SourcePointer

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

def RepresentsAt (color : α → C) (q : C) (source : Cursor α ρ) :
    Option (Cursor α (List ρ)) → Prop
  | none => q ∉ source.tree.support color
  | some actual => ColoredStorage.Represents color q source actual

def Represents (color : α → C) (source : Cursor α ρ) (state : State C α ρ) : Prop :=
  ∀ q, RepresentsAt color q source (state q)

theorem source_step [Fintype C] (color : α → C) {source final : Cursor α ρ}
    (step : SourcePointer.Step source final) {state : State C α ρ}
    (represented : Represents color source state) :
    ∃ actual reads cost, Trace state reads actual cost ∧ cost ≤ 17 * Fintype.card C ∧
      Represents color final actual := by
  classical
  have support : source.tree.support color = final.tree.support color := by
    rw [Source.support_leaves,Source.support_leaves,step.leaves]
  have each : ∀ q, ∃ actual cost, LocalTrace (state q) actual cost ∧ cost ≤ 17 ∧
      RepresentsAt color q final actual := by
    intro q
    have h := represented q
    cases cursor : state q with
    | none =>
      rw [cursor] at h
      exact ⟨none,0,rfl,Nat.zero_le _,by simpa only [RepresentsAt,← support] using h⟩
    | some physical =>
      rw [cursor] at h
      obtain ⟨actual,reads,cost,trace,bound,fresh⟩ := represented_step color q step h
      exact ⟨some actual,cost,⟨reads,trace⟩,bound,fresh⟩
  choose actual costs traces bounds fresh using each
  obtain ⟨reads,trace⟩ := batch_all state actual costs traces
  refine ⟨actual,reads,_,trace,?_,fresh⟩
  calc
    ∑ q, costs q ≤ ∑ _q : C, 17 := Finset.sum_le_sum (fun q _ => bounds q)
    _ = 17 * Fintype.card C := by simp [Nat.mul_comm]

theorem support_focus (color : α → C) (focus : Source α ρ) (ancestors : List (Frame α ρ)) :
    focus.support color ⊆ (plug focus ancestors).support color := by
  induction ancestors generalizing focus with
  | nil => exact Finset.Subset.refl _
  | cons frame rest ih =>
    cases frame with
    | left record r =>
      exact Finset.Subset.trans Finset.subset_union_left (ih (.fork record focus r))
    | right l record =>
      exact Finset.Subset.trans Finset.subset_union_right (ih (.fork record l focus))

theorem source_read [Fintype C] (color : α → C) (source : Cursor α ρ) (state : State C α ρ)
    (represented : Represents color source state) :
    ∃ records, Trace state [(source.focus.rootOwner color,records)] state 1 ∧
      source.focus.rootRecord ∈ records ∧ records.length ≤ Fintype.card C := by
  let owner := source.focus.rootOwner color
  have member : owner ∈ source.tree.support color :=
    support_focus color source.focus source.ancestors (Source.rootOwner_mem color source.focus)
  have h := represented owner
  cases cursor : state owner with
  | none =>
    rw [cursor] at h
    exact False.elim (h member)
  | some actual =>
    rw [cursor] at h
    obtain ⟨_,found,bounded⟩ := read_record color source h
    exact ⟨actual.focus.rootRecord,.read cursor (.nil _),found,bounded⟩

theorem source_trace [Fintype C] (color : α → C)
    {source final : Cursor α ρ} {sourceReads : List ρ} {sourceCost : Nat}
    (execution : SourcePointer.Trace source sourceReads final sourceCost)
    {state : State C α ρ} (represented : Represents color source state) :
    ∃ actual reads cost, Trace state reads actual cost ∧ cost ≤ (17 * Fintype.card C) * sourceCost ∧
      Represents color final actual := by
  induction execution generalizing state with
  | nil source => exact ⟨state,[],0,.nil _,Nat.zero_le _,represented⟩
  | step move rest ih =>
    obtain ⟨middle,firstReads,firstCost,first,firstBound,middleRep⟩ := source_step color move represented
    obtain ⟨actual,lastReads,lastCost,last,lastBound,finalRep⟩ := ih middleRep
    exact ⟨actual,_,_,first.append last,by rw [Nat.mul_add,Nat.mul_one]; omega,finalRep⟩
  | @read source final reads cost rest ih =>
    obtain ⟨records,first,_,_⟩ := source_read color source state represented
    obtain ⟨actual,lastReads,lastCost,last,lastBound,finalRep⟩ := ih represented
    have positive : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨source.focus.rootOwner color⟩
    exact ⟨actual,_,_,first.append last,by rw [Nat.mul_add,Nat.mul_one]; omega,finalRep⟩

def roots (color : α → C) (source : Source α ρ) : State C α ρ :=
  fun q => (packed color q source).map (fun actual => ⟨actual,[]⟩)

theorem represents_roots (color : α → C) (source : Source α ρ) :
    Represents color ⟨source,[]⟩ (roots color source) := by
  intro q
  unfold roots
  cases present : packed color q source with
  | none => exact (packed_none_iff color q source).mp present
  | some actual => exact represents_root color q source present

end TangoSquared.Paper20261030.ProjectionForest
