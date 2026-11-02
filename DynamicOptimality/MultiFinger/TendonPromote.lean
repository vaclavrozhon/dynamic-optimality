import DynamicOptimality.MultiFinger.TendonAlgebra

/-! Promoting either source endpoint of a compressed tendon.
Exactly one half-tendon deque changes; every hanging source subtree and
both actual endpoint key identities are retained. -/

namespace DynamicOptimality.MultiFinger.TendonContents

open ChaCha.MTR
open Pointer (MarkedTree)
open GeometricOnlineSimulation.OpenDeque
open TendonSource

variable {α : Type*}

theorem Tendon.outer_right_pop {tendon : Tendon α} {frames : List (Pointer.Frame α)}
    (gap : RawTree α) (key : α)
    (valid : tendon.Represents (frames++[.right gap key])) (inside : MarkedTree α) :
    ∃ after : Tendon α, ∃ count : Nat, after.Represents frames ∧
      RegionStep (tendon.marked inside) (.node (.hole gap) key (after.marked inside)) count ∧
      count+after.potential ≤ tendon.potential+14 := by
  have lowValid : LowRep tendon.lowQueue ((gap,key)::low frames) := by
    simpa only [low_append,low,List.nil_append,List.singleton_append] using valid.1
  have highValid : HighRep tendon.highQueue (high frames) := by
    simpa only [high_append,high,List.append_nil] using valid.2
  obtain ⟨queue,count,queueValid,actual,paid⟩ := low_pop_first lowValid (firstHole (highMarked tendon.highQueue inside))
  let after : Tendon α := ⟨queue,tendon.highQueue⟩
  refine ⟨after,count,⟨queueValid,highValid⟩,
    low_first_region tendon.lowQueue queue gap key (highMarked tendon.highQueue inside) actual,?_⟩
  simp only [Tendon.potential,after,lowPotential] at paid ⊢
  omega

theorem Tendon.outer_left_pop {tendon : Tendon α} {frames : List (Pointer.Frame α)}
    (gap : RawTree α) (key : α)
    (valid : tendon.Represents (frames++[.left key gap])) (inside : MarkedTree α) :
    ∃ after : Tendon α, ∃ count : Nat, after.Represents frames ∧
      RegionStep (tendon.marked inside) (.node (after.marked inside) key (.hole gap)) count ∧
      count+after.potential ≤ tendon.potential+14 := by
  have lowValid : LowRep tendon.lowQueue (low frames) := by
    simpa only [low_append,low,List.nil_append] using valid.1
  have highValid : HighRep tendon.highQueue (high frames++[(key,gap)]) := by
    simpa only [high_append,high] using valid.2
  obtain ⟨queue,count,queueValid,actual,paid⟩ := high_pop_last highValid (lastHole inside)
  let after : Tendon α := ⟨tendon.lowQueue,queue⟩
  have step := (high_last_region tendon.highQueue queue gap key inside actual).low tendon.lowQueue
  refine ⟨after,count,⟨lowValid,queueValid⟩,step.congr (.refl _) ?_,?_⟩
  · exact low_node tendon.lowQueue (highMarked queue inside) (.hole gap) key
  · simp only [Tendon.potential,after,highPotential] at paid ⊢
    omega

theorem Tendon.inner_left_pop {tendon : Tendon α} {frames : List (Pointer.Frame α)}
    (gap : RawTree α) (key : α)
    (valid : tendon.Represents (.left key gap::frames)) (inside : MarkedTree α) :
    ∃ after : Tendon α, ∃ count : Nat, after.Represents frames ∧
      RegionStep (tendon.marked inside) (after.marked (.node inside key (.hole gap))) count ∧
      count+after.potential ≤ tendon.potential+14 := by
  obtain ⟨queue,count,queueValid,actual,paid⟩ := high_pop_first valid.2 (lastHole inside)
  let after : Tendon α := ⟨tendon.lowQueue,queue⟩
  have step := (high_first_region tendon.highQueue queue gap key inside actual).low tendon.lowQueue
  refine ⟨after,count,⟨valid.1,queueValid⟩,step.congr (.refl _) ?_,?_⟩
  · exact (high_node queue inside (.hole gap) key).symm.low tendon.lowQueue
  · simp only [Tendon.potential,after,highPotential] at paid ⊢
    omega

theorem Tendon.inner_right_pop {tendon : Tendon α} {frames : List (Pointer.Frame α)}
    (gap : RawTree α) (key : α)
    (valid : tendon.Represents (.right gap key::frames)) (inside : MarkedTree α) :
    ∃ after : Tendon α, ∃ count : Nat, after.Represents frames ∧
      RegionStep (tendon.marked inside) (after.marked (.node (.hole gap) key inside)) count ∧
      count+after.potential ≤ tendon.potential+14 := by
  obtain ⟨queue,count,queueValid,actual,paid⟩ := low_pop_last valid.1 (firstHole (highMarked tendon.highQueue inside))
  let after : Tendon α := ⟨queue,tendon.highQueue⟩
  have step := low_last_region tendon.lowQueue queue gap key (highMarked tendon.highQueue inside) actual
  refine ⟨after,count,⟨queueValid,valid.2⟩,step.congr (.refl _) ?_,?_⟩
  · exact ((high_node tendon.highQueue (.hole gap) inside key).low queue |>.trans
      (low_node queue (.hole gap) (highMarked tendon.highQueue inside) key)).symm
  · simp only [Tendon.potential,after,lowPotential] at paid ⊢
    omega

end DynamicOptimality.MultiFinger.TendonContents
