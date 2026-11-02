import DynamicOptimality.MultiFinger.TendonSingleton

/-! Total physical endpoint operations, including empty half-tendons.
The optional representation permits popping the last separator or pushing
into an empty tendon without changing the original key universe. -/

namespace DynamicOptimality.MultiFinger.TendonContents

open ChaCha.MTR SingleFinger SearchRotation
open DynamicOptimality.GeometricOnlineSimulation.OpenDeque
open TendonSource

variable {α : Type*}

def lowPotential (queue : Option (Right α)) : Nat :=
  (queue.map Right.potential).getD 0

def highPotential (queue : Option (Left α)) : Nat :=
  (queue.map Left.potential).getD 0

theorem low_pop_first {queue : Option (Right α)} {rest : List (LowCell α)}
    {gap : RawTree α} {key : α} (valid : LowRep queue ((gap,key)::rest)) (inside : RawTree α) :
    ∃ after : Option (Right α), ∃ count : Nat, LowRep after rest ∧
      Rotations (lowFill queue inside) (.node gap key (lowFill after inside)) count ∧
      count+lowPotential after ≤ lowPotential queue+14 := by
  cases queue with
  | none => simp [LowRep] at valid
  | some layout =>
      by_cases empty : rest = []
      · subst rest
        have single := low_singleton layout key gap valid inside
        refine ⟨none,0,rfl,?_,?_⟩
        · simpa only [lowFill,single.1] using Rotations.refl (.node gap key inside)
        · simp [lowPotential]
      · obtain ⟨after,count,validAfter,actual,paid⟩ := low_pop_min layout valid empty inside
        exact ⟨some after,count,validAfter,actual,paid⟩

theorem low_pop_last {queue : Option (Right α)} {rest : List (LowCell α)}
    {gap : RawTree α} {key : α} (valid : LowRep queue (rest++[(gap,key)])) (inside : RawTree α) :
    ∃ after : Option (Right α), ∃ count : Nat, LowRep after rest ∧
      Rotations (lowFill queue inside) (.node (lowFill after gap) key inside) count ∧
      count+lowPotential after ≤ lowPotential queue+14 := by
  cases queue with
  | none => simp [LowRep] at valid
  | some layout =>
      by_cases empty : rest = []
      · subst rest
        have single := low_singleton layout key gap valid inside
        refine ⟨none,0,rfl,?_,?_⟩
        · simpa only [lowFill,single.1] using Rotations.refl (.node gap key inside)
        · simp [lowPotential]
      · obtain ⟨after,count,validAfter,actual,paid⟩ := low_pop_max layout valid empty inside
        exact ⟨some after,count,validAfter,actual,paid⟩

theorem high_pop_first {queue : Option (Left α)} {rest : List (HighCell α)}
    {gap : RawTree α} {key : α} (valid : HighRep queue ((key,gap)::rest)) (inside : RawTree α) :
    ∃ after : Option (Left α), ∃ count : Nat, HighRep after rest ∧
      Rotations (highFill queue inside) (.node inside key (highFill after gap)) count ∧
      count+highPotential after ≤ highPotential queue+14 := by
  cases queue with
  | none => simp [HighRep] at valid
  | some layout =>
      by_cases empty : rest = []
      · subst rest
        have single := high_singleton layout key gap valid inside
        refine ⟨none,0,rfl,?_,?_⟩
        · simpa only [highFill,single.1] using Rotations.refl (.node inside key gap)
        · simp [highPotential]
      · obtain ⟨after,count,validAfter,actual,paid⟩ := high_pop_min layout valid empty inside
        exact ⟨some after,count,validAfter,actual,paid⟩

theorem high_pop_last {queue : Option (Left α)} {rest : List (HighCell α)}
    {gap : RawTree α} {key : α} (valid : HighRep queue (rest++[(key,gap)])) (inside : RawTree α) :
    ∃ after : Option (Left α), ∃ count : Nat, HighRep after rest ∧
      Rotations (highFill queue inside) (.node (highFill after inside) key gap) count ∧
      count+highPotential after ≤ highPotential queue+14 := by
  cases queue with
  | none => simp [HighRep] at valid
  | some layout =>
      by_cases empty : rest = []
      · subst rest
        have single := high_singleton layout key gap valid inside
        refine ⟨none,0,rfl,?_,?_⟩
        · simpa only [highFill,single.1] using Rotations.refl (.node inside key gap)
        · simp [highPotential]
      · obtain ⟨after,count,validAfter,actual,paid⟩ := high_pop_max layout valid empty inside
        exact ⟨some after,count,validAfter,actual,paid⟩

theorem low_insert_first {queue : Option (Right α)} {cells : List (LowCell α)}
    (valid : LowRep queue cells) (gap inside : RawTree α) (key : α) :
    ∃ after : Option (Right α), ∃ count : Nat, LowRep after ((gap,key)::cells) ∧
      Rotations (.node gap key (lowFill queue inside)) (lowFill after inside) count ∧
      count+lowPotential after ≤ lowPotential queue+5 := by
  cases queue with
  | none =>
      subst cells
      obtain ⟨after,valid,paid,shape⟩ := low_singleton_create key gap
      refine ⟨some after,0,valid,?_,?_⟩
      · simpa only [lowFill,shape] using Rotations.refl (.node gap key inside)
      · simp [lowPotential,paid]
  | some layout =>
      obtain ⟨after,count,validAfter,actual,paid⟩ := low_push_first layout valid gap inside key
      exact ⟨some after,count,validAfter,actual,paid⟩

theorem low_insert_last {queue : Option (Right α)} {cells : List (LowCell α)}
    (valid : LowRep queue cells) (gap inside : RawTree α) (key : α) :
    ∃ after : Option (Right α), ∃ count : Nat, LowRep after (cells++[(gap,key)]) ∧
      Rotations (lowFill queue (.node gap key inside)) (lowFill after inside) count ∧
      count+lowPotential after ≤ lowPotential queue+5 := by
  cases queue with
  | none =>
      subst cells
      obtain ⟨after,valid,paid,shape⟩ := low_singleton_create key gap
      refine ⟨some after,0,valid,?_,?_⟩
      · simpa only [lowFill,shape] using Rotations.refl (.node gap key inside)
      · simp [lowPotential,paid]
  | some layout =>
      obtain ⟨after,count,validAfter,actual,paid⟩ := low_push_last layout valid gap inside key
      exact ⟨some after,count,validAfter,actual,paid⟩

theorem high_insert_first {queue : Option (Left α)} {cells : List (HighCell α)}
    (valid : HighRep queue cells) (gap inside : RawTree α) (key : α) :
    ∃ after : Option (Left α), ∃ count : Nat, HighRep after ((key,gap)::cells) ∧
      Rotations (highFill queue (.node inside key gap)) (highFill after inside) count ∧
      count+highPotential after ≤ highPotential queue+5 := by
  cases queue with
  | none =>
      subst cells
      obtain ⟨after,valid,paid,shape⟩ := high_singleton_create key gap
      refine ⟨some after,0,valid,?_,?_⟩
      · simpa only [highFill,shape] using Rotations.refl (.node inside key gap)
      · simp [highPotential,paid]
  | some layout =>
      obtain ⟨after,count,validAfter,actual,paid⟩ := high_push_first layout valid gap inside key
      exact ⟨some after,count,validAfter,actual,paid⟩

theorem high_insert_last {queue : Option (Left α)} {cells : List (HighCell α)}
    (valid : HighRep queue cells) (gap inside : RawTree α) (key : α) :
    ∃ after : Option (Left α), ∃ count : Nat, HighRep after (cells++[(key,gap)]) ∧
      Rotations (.node (highFill queue inside) key gap) (highFill after inside) count ∧
      count+highPotential after ≤ highPotential queue+5 := by
  cases queue with
  | none =>
      subst cells
      obtain ⟨after,valid,paid,shape⟩ := high_singleton_create key gap
      refine ⟨some after,0,valid,?_,?_⟩
      · simpa only [highFill,shape] using Rotations.refl (.node inside key gap)
      · simp [highPotential,paid]
  | some layout =>
      obtain ⟨after,count,validAfter,actual,paid⟩ := high_push_last layout valid gap inside key
      exact ⟨some after,count,validAfter,actual,paid⟩

end DynamicOptimality.MultiFinger.TendonContents
