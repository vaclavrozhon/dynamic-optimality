import DynamicOptimality.MultiFinger.TendonPromote

/-! Demoting a source endpoint into its adjacent persistent tendon.
The consumed separator remains an ordinary key of the physical BST. -/

namespace DynamicOptimality.MultiFinger.TendonContents

open ChaCha.MTR
open Pointer (MarkedTree)
open GeometricOnlineSimulation.OpenDeque
open TendonSource

variable {α : Type*}

theorem Tendon.outer_right_push {tendon : Tendon α} {frames : List (Pointer.Frame α)}
    (gap : RawTree α) (key : α) (valid : tendon.Represents frames) (inside : MarkedTree α) :
    ∃ after : Tendon α, ∃ count : Nat, after.Represents (frames++[.right gap key]) ∧
      RegionStep (.node (.hole gap) key (tendon.marked inside)) (after.marked inside) count ∧
      count+after.potential ≤ tendon.potential+5 := by
  obtain ⟨queue,count,queueValid,actual,paid⟩ :=
    low_insert_first valid.1 gap (firstHole (highMarked tendon.highQueue inside)) key
  let after : Tendon α := ⟨queue,tendon.highQueue⟩
  refine ⟨after,count,⟨?_,?_⟩,
    (low_first_region queue tendon.lowQueue gap key (highMarked tendon.highQueue inside) actual.symm).symm,?_⟩
  · simpa only [low_append,low,List.nil_append,List.singleton_append] using queueValid
  · simpa only [high_append,high,List.append_nil] using valid.2
  · simp only [Tendon.potential,after,lowPotential] at paid ⊢
    omega

theorem Tendon.outer_left_push {tendon : Tendon α} {frames : List (Pointer.Frame α)}
    (gap : RawTree α) (key : α) (valid : tendon.Represents frames) (inside : MarkedTree α) :
    ∃ after : Tendon α, ∃ count : Nat, after.Represents (frames++[.left key gap]) ∧
      RegionStep (.node (tendon.marked inside) key (.hole gap)) (after.marked inside) count ∧
      count+after.potential ≤ tendon.potential+5 := by
  obtain ⟨queue,count,queueValid,actual,paid⟩ := high_insert_last valid.2 gap (lastHole inside) key
  let after : Tendon α := ⟨tendon.lowQueue,queue⟩
  have step := (high_last_region queue tendon.highQueue gap key inside actual.symm).symm.low tendon.lowQueue
  refine ⟨after,count,⟨?_,?_⟩,step.congr ?_ (.refl _),?_⟩
  · simpa only [low_append,low,List.nil_append] using valid.1
  · simpa only [high_append,high] using queueValid
  · exact low_node tendon.lowQueue (highMarked tendon.highQueue inside) (.hole gap) key
  · simp only [Tendon.potential,after,highPotential] at paid ⊢
    omega

theorem Tendon.inner_left_push {tendon : Tendon α} {frames : List (Pointer.Frame α)}
    (gap : RawTree α) (key : α) (valid : tendon.Represents frames) (inside : MarkedTree α) :
    ∃ after : Tendon α, ∃ count : Nat, after.Represents (.left key gap::frames) ∧
      RegionStep (tendon.marked (.node inside key (.hole gap))) (after.marked inside) count ∧
      count+after.potential ≤ tendon.potential+5 := by
  obtain ⟨queue,count,queueValid,actual,paid⟩ := high_insert_first valid.2 gap (lastHole inside) key
  let after : Tendon α := ⟨tendon.lowQueue,queue⟩
  have step := (high_first_insert_region tendon.highQueue queue gap key inside actual).low tendon.lowQueue
  refine ⟨after,count,⟨valid.1,queueValid⟩,step,?_⟩
  simp only [Tendon.potential,after,highPotential] at paid ⊢
  omega

theorem Tendon.inner_right_push {tendon : Tendon α} {frames : List (Pointer.Frame α)}
    (gap : RawTree α) (key : α) (valid : tendon.Represents frames) (inside : MarkedTree α) :
    ∃ after : Tendon α, ∃ count : Nat, after.Represents (.right gap key::frames) ∧
      RegionStep (tendon.marked (.node (.hole gap) key inside)) (after.marked inside) count ∧
      count+after.potential ≤ tendon.potential+5 := by
  obtain ⟨queue,count,queueValid,actual,paid⟩ :=
    low_insert_last valid.1 gap (firstHole (highMarked tendon.highQueue inside)) key
  let after : Tendon α := ⟨queue,tendon.highQueue⟩
  have step := low_last_insert_region tendon.lowQueue queue gap key (highMarked tendon.highQueue inside) actual
  refine ⟨after,count,⟨queueValid,valid.2⟩,step.congr ?_ (.refl _),?_⟩
  · exact (high_node tendon.highQueue (.hole gap) inside key).symm.low tendon.lowQueue
  · simp only [Tendon.potential,after,lowPotential] at paid ⊢
    omega

end DynamicOptimality.MultiFinger.TendonContents
