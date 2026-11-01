import Splay.Lazy.CanonicalTrace
import Splay.Lazy.OperationValidity
import Splay.Interface.Potential

namespace Splay.Lazy

namespace State

/-- Apply a fixed number of permitted unit decreases to one rich value. -/
def decreaseValueN {n : ℕ} (state : State n)
    (element : Element n) : ℕ → State n
  | 0 => state
  | steps + 1 =>
      (state.decreaseValue element).decreaseValueN element steps

/-- Apply a fixed number of permitted unit increases to one rich value. -/
def increaseValueN {n : ℕ} (state : State n)
    (element : Element n) : ℕ → State n
  | 0 => state
  | steps + 1 =>
      (state.increaseValue element).increaseValueN element steps

@[simp]
theorem decreaseValueN_zero {n : ℕ} (state : State n)
    (element : Element n) :
    state.decreaseValueN element 0 = state :=
  rfl

@[simp]
theorem increaseValueN_zero {n : ℕ} (state : State n)
    (element : Element n) :
    state.increaseValueN element 0 = state :=
  rfl

@[simp]
theorem decreaseValueN_value_self {n : ℕ} (state : State n)
    (element : Element n) (steps : ℕ) :
    (state.decreaseValueN element steps).value element =
      state.value element - steps := by
  induction steps generalizing state with
  | zero =>
      rfl
  | succ steps ih =>
      rw [decreaseValueN]
      rw [ih]
      simp [decreaseValue]
      omega

@[simp]
theorem increaseValueN_value_self {n : ℕ} (state : State n)
    (element : Element n) (steps : ℕ) :
    (state.increaseValueN element steps).value element =
      state.value element + steps := by
  induction steps generalizing state with
  | zero =>
      rfl
  | succ steps ih =>
      rw [increaseValueN]
      rw [ih]
      simp [increaseValue]
      omega

@[simp]
theorem decreaseValueN_value_of_ne {n : ℕ} (state : State n)
    {element other : Element n} (different : other ≠ element)
    (steps : ℕ) :
    (state.decreaseValueN element steps).value other =
      state.value other := by
  induction steps generalizing state with
  | zero =>
      rfl
  | succ steps ih =>
      rw [decreaseValueN, ih]
      simp [decreaseValue, different]

@[simp]
theorem increaseValueN_value_of_ne {n : ℕ} (state : State n)
    {element other : Element n} (different : other ≠ element)
    (steps : ℕ) :
    (state.increaseValueN element steps).value other =
      state.value other := by
  induction steps generalizing state with
  | zero =>
      rfl
  | succ steps ih =>
      rw [increaseValueN, ih]
      simp [increaseValue, different]

@[simp]
theorem decreaseValueN_blocks {n : ℕ} (state : State n)
    (element : Element n) (steps : ℕ) :
    (state.decreaseValueN element steps).blocks = state.blocks := by
  induction steps generalizing state with
  | zero =>
      rfl
  | succ steps ih =>
      rw [decreaseValueN, ih]
      rfl

@[simp]
theorem increaseValueN_blocks {n : ℕ} (state : State n)
    (element : Element n) (steps : ℕ) :
    (state.increaseValueN element steps).blocks = state.blocks := by
  induction steps generalizing state with
  | zero =>
      rfl
  | succ steps ih =>
      rw [increaseValueN, ih]
      rfl

@[simp]
theorem decreaseValueN_view {n : ℕ} (state : State n)
    (element : Element n) (steps : ℕ) :
    (state.decreaseValueN element steps).view = state.view := by
  induction steps generalizing state with
  | zero =>
      rfl
  | succ steps ih =>
      rw [decreaseValueN, ih]
      rfl

@[simp]
theorem increaseValueN_view {n : ℕ} (state : State n)
    (element : Element n) (steps : ℕ) :
    (state.increaseValueN element steps).view = state.view := by
  induction steps generalizing state with
  | zero =>
      rfl
  | succ steps ih =>
      rw [increaseValueN, ih]
      rfl

/--
Repeated decreases form a rich trace whenever the final value stays positive.
-/
theorem decreaseValueN_trace {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (element : Element n) (steps : ℕ)
    (valid : state.Valid params)
    (staysPositive : steps < state.value element) :
    Trace params state
      (List.replicate steps
        (.operation (.valueChange element .decrease)))
      (state.decreaseValueN element steps) := by
  induction steps generalizing state with
  | zero =>
      exact Trace.nil valid
  | succ steps ih =>
      have canDecrease : 1 < state.value element := by
        omega
      have afterValid :=
        state.decreaseValue_valid element valid canDecrease
      have tailPositive :
          steps < (state.decreaseValue element).value element := by
        simp [decreaseValue]
        omega
      exact
        Trace.cons
          (state.decreaseValue_step element valid canDecrease)
          (ih (state.decreaseValue element) afterValid tailPositive)

/--
Repeated increases form a rich trace whenever the final value stays within
the interface bound.
-/
theorem increaseValueN_trace {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (element : Element n) (steps : ℕ)
    (valid : state.Valid params)
    (withinBound :
      state.value element + steps ≤ params.valueBound) :
    Trace params state
      (List.replicate steps
        (.operation (.valueChange element .increase)))
      (state.increaseValueN element steps) := by
  induction steps generalizing state with
  | zero =>
      exact Trace.nil valid
  | succ steps ih =>
      have canIncrease :
          state.value element < params.valueBound := by
        omega
      have afterValid :=
        state.increaseValue_valid element valid canIncrease
      have tailBound :
          (state.increaseValue element).value element + steps ≤
            params.valueBound := by
        simp [increaseValue]
        omega
      exact
        Trace.cons
          (state.increaseValue_step element valid canIncrease)
          (ih (state.increaseValue element) afterValid tailBound)

/-- Normalize one value to an arbitrary bounded positive target by unit steps. -/
def adjustValue {n : ℕ} (state : State n)
    (element : Element n) (target : ℕ) : State n :=
  if target ≤ state.value element then
    state.decreaseValueN element (state.value element - target)
  else
    state.increaseValueN element (target - state.value element)

/-- Visible rich events emitted by `adjustValue`. -/
def adjustValueEvents {n : ℕ} (state : State n)
    (element : Element n) (target : ℕ) : List (Event n) :=
  if target ≤ state.value element then
    List.replicate (state.value element - target)
      (.operation (.valueChange element .decrease))
  else
    List.replicate (target - state.value element)
      (.operation (.valueChange element .increase))

@[simp]
theorem adjustValue_value_self {n : ℕ} (state : State n)
    (element : Element n) (target : ℕ)
    (positive : 1 ≤ target) :
    (state.adjustValue element target).value element = target := by
  unfold adjustValue
  split
  next targetLe =>
    rw [decreaseValueN_value_self]
    omega
  next notTargetLe =>
    rw [increaseValueN_value_self]
    omega

@[simp]
theorem adjustValue_value_of_ne {n : ℕ} (state : State n)
    {element other : Element n} (different : other ≠ element)
    (target : ℕ) :
    (state.adjustValue element target).value other =
      state.value other := by
  unfold adjustValue
  split
  · exact decreaseValueN_value_of_ne state different _
  · exact increaseValueN_value_of_ne state different _

@[simp]
theorem adjustValue_blocks {n : ℕ} (state : State n)
    (element : Element n) (target : ℕ) :
    (state.adjustValue element target).blocks = state.blocks := by
  unfold adjustValue
  split <;> simp

@[simp]
theorem adjustValue_view {n : ℕ} (state : State n)
    (element : Element n) (target : ℕ) :
    (state.adjustValue element target).view = state.view := by
  unfold adjustValue
  split <;> simp

/-- Every positive bounded target is reachable by a finite rich value trace. -/
theorem adjustValue_trace {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (element : Element n) (target : ℕ)
    (valid : state.Valid params)
    (positive : 1 ≤ target)
    (bounded : target ≤ params.valueBound) :
    Trace params state (state.adjustValueEvents element target)
      (state.adjustValue element target) := by
  unfold adjustValueEvents adjustValue
  split
  next targetLe =>
    apply state.decreaseValueN_trace element
      (state.value element - target) valid
    omega
  next notTargetLe =>
    apply state.increaseValueN_trace element
      (target - state.value element) valid
    omega

@[simp]
theorem eraseOperations_adjustValueEvents {n : ℕ}
    (state : State n) (element : Element n) (target : ℕ) :
    eraseOperations (state.adjustValueEvents element target) =
      if target ≤ state.value element then
        List.replicate (state.value element - target)
          (.valueChange element .decrease)
      else
        List.replicate (target - state.value element)
          (.valueChange element .increase) := by
  unfold adjustValueEvents
  split <;>
    simp [eraseOperations, Event.operations, List.flatMap_replicate]

@[simp]
theorem totalValueChanges_adjustValueEvents {n : ℕ}
    (state : State n) (element : Element n) (target : ℕ) :
    Interface.totalValueChanges
        (eraseOperations (state.adjustValueEvents element target)) =
      (state.adjustValueEvents element target).length := by
  unfold adjustValueEvents
  split <;>
    simp [eraseOperations, Event.operations,
      Interface.totalValueChanges,
      Interface.Operation.valueChangeCount,
      List.flatMap_replicate]

@[simp]
theorem totalInserts_adjustValueEvents {n : ℕ}
    (state : State n) (element : Element n) (target : ℕ) :
    Interface.totalInserts
        (eraseOperations (state.adjustValueEvents element target)) = 0 := by
  unfold adjustValueEvents
  split <;>
    simp [eraseOperations, Event.operations,
      Interface.totalInserts,
      Interface.Operation.insertCount,
      List.flatMap_replicate]

/--
Adjusting between two values already inside the interface range needs at most
`valueBound` visible unit changes.
-/
theorem adjustValueEvents_length_le {n : ℕ}
    {params : Interface.Parameters} {state : State n}
    (element : Element n) (target : ℕ)
    (valid : state.Valid params)
    (bounded : target ≤ params.valueBound) :
    (state.adjustValueEvents element target).length ≤
      params.valueBound := by
  have currentBound := (valid.toInterface.2.1 element).2
  change state.value element ≤ params.valueBound at currentBound
  unfold adjustValueEvents
  split <;> simp only [List.length_replicate] <;> omega

/-- Normalize a list of elements to pointwise targets, in list order. -/
def adjustValues {n : ℕ} (state : State n)
    (target : Element n → ℕ) : List (Element n) → State n
  | [] => state
  | element :: elements =>
      (state.adjustValue element (target element)).adjustValues target elements

/-- Visible unit value changes emitted by `adjustValues`. -/
def adjustValuesEvents {n : ℕ} (state : State n)
    (target : Element n → ℕ) : List (Element n) → List (Event n)
  | [] => []
  | element :: elements =>
      state.adjustValueEvents element (target element) ++
        (state.adjustValue element (target element)).adjustValuesEvents
          target elements

@[simp]
theorem adjustValues_nil {n : ℕ} (state : State n)
    (target : Element n → ℕ) :
    state.adjustValues target [] = state := rfl

@[simp]
theorem adjustValuesEvents_nil {n : ℕ} (state : State n)
    (target : Element n → ℕ) :
    state.adjustValuesEvents target [] = [] := rfl

@[simp]
theorem adjustValuesEvents_cons {n : ℕ} (state : State n)
    (target : Element n → ℕ) (element : Element n)
    (elements : List (Element n)) :
    state.adjustValuesEvents target (element :: elements) =
      state.adjustValueEvents element (target element) ++
        (state.adjustValue element (target element)).adjustValuesEvents
          target elements := rfl

@[simp]
theorem adjustValues_blocks {n : ℕ} (state : State n)
    (target : Element n → ℕ) (elements : List (Element n)) :
    (state.adjustValues target elements).blocks = state.blocks := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      rw [adjustValues, ih, adjustValue_blocks]

@[simp]
theorem adjustValues_view {n : ℕ} (state : State n)
    (target : Element n → ℕ) (elements : List (Element n)) :
    (state.adjustValues target elements).view = state.view := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      rw [adjustValues, ih, adjustValue_view]

@[simp]
theorem adjustValues_value_of_not_mem {n : ℕ} (state : State n)
    (target : Element n → ℕ) (elements : List (Element n))
    {queried : Element n} (notMember : queried ∉ elements) :
    (state.adjustValues target elements).value queried =
      state.value queried := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      have parts : queried ≠ element ∧ queried ∉ elements := by
        simpa only [List.mem_cons, not_or] using notMember
      rw [adjustValues, ih (state := state.adjustValue element (target element))
        parts.2, adjustValue_value_of_ne state parts.1]

@[simp]
theorem adjustValues_value_of_mem {n : ℕ} (state : State n)
    (target : Element n → ℕ) {elements : List (Element n)}
    (nodup : elements.Nodup) {queried : Element n}
    (member : queried ∈ elements)
    (positive : ∀ element ∈ elements, 1 ≤ target element) :
    (state.adjustValues target elements).value queried = target queried := by
  induction elements generalizing state with
  | nil => simp at member
  | cons element elements ih =>
      have nodupParts := List.nodup_cons.mp nodup
      rcases List.mem_cons.mp member with rfl | tailMember
      · rw [adjustValues,
          adjustValues_value_of_not_mem _ _ _ nodupParts.1]
        exact adjustValue_value_self state queried (target queried)
          (positive queried (by simp))
      · apply ih (state := state.adjustValue element (target element))
          nodupParts.2 tailMember
        intro candidate candidateMember
        exact positive candidate (by simp [candidateMember])

/-- Pointwise positive bounded targets admit one checked concatenated trace. -/
theorem adjustValues_trace {n : ℕ}
    {params : Interface.Parameters} (state : State n)
    (target : Element n → ℕ) (elements : List (Element n))
    (valid : state.Valid params)
    (positive : ∀ element ∈ elements, 1 ≤ target element)
    (bounded : ∀ element ∈ elements,
      target element ≤ params.valueBound) :
    Trace params state (state.adjustValuesEvents target elements)
      (state.adjustValues target elements) := by
  induction elements generalizing state with
  | nil => exact Trace.nil valid
  | cons element elements ih =>
      have headTrace := state.adjustValue_trace element (target element)
        valid (positive element (by simp)) (bounded element (by simp))
      have tailTrace := ih (state.adjustValue element (target element))
        headTrace.final_valid
        (by
          intro candidate candidateMember
          exact positive candidate (by simp [candidateMember]))
        (by
          intro candidate candidateMember
          exact bounded candidate (by simp [candidateMember]))
      exact headTrace.append tailTrace

/-- Pointwise normalization consists solely of value changes. -/
theorem totalInserts_adjustValuesEvents_eq_zero {n : ℕ}
    (state : State n) (target : Element n → ℕ)
    (elements : List (Element n)) :
    Interface.totalInserts
        (eraseOperations (state.adjustValuesEvents target elements)) = 0 := by
  induction elements generalizing state with
  | nil => simp [adjustValuesEvents, eraseOperations,
      Interface.totalInserts]
  | cons element elements ih =>
      rw [adjustValuesEvents_cons, eraseOperations_append]
      have headZero := state.totalInserts_adjustValueEvents
        element (target element)
      have tailZero := ih
        (state := state.adjustValue element (target element))
      rw [show Interface.totalInserts
            (eraseOperations
                (state.adjustValueEvents element (target element)) ++
              eraseOperations
                ((state.adjustValue element (target element))
                  |>.adjustValuesEvents target elements)) =
            Interface.totalInserts
                (eraseOperations
                  (state.adjustValueEvents element (target element))) +
              Interface.totalInserts
                (eraseOperations
                  ((state.adjustValue element (target element))
                    |>.adjustValuesEvents target elements)) by
          simp [Interface.totalInserts]]
      rw [headZero, tailZero, zero_add]

theorem totalIncreases_adjustValueEvents_eq_zero_of_le {n : ℕ}
    (state : State n) (element : Element n) (target : ℕ)
    (targetLe : target ≤ state.value element) :
    Interface.totalIncreases
        (eraseOperations (state.adjustValueEvents element target)) = 0 := by
  rw [eraseOperations_adjustValueEvents, if_pos targetLe]
  simp [Interface.totalIncreases, Interface.Operation.increaseCount]

/-- Pointwise downward normalization emits no increasing value change. -/
theorem totalIncreases_adjustValuesEvents_eq_zero_of_le {n : ℕ}
    (state : State n) (target : Element n → ℕ)
    (elements : List (Element n)) (nodup : elements.Nodup)
    (targetLe : ∀ element ∈ elements,
      target element ≤ state.value element) :
    Interface.totalIncreases
        (eraseOperations (state.adjustValuesEvents target elements)) = 0 := by
  induction elements generalizing state with
  | nil => simp [adjustValuesEvents, eraseOperations,
      Interface.totalIncreases]
  | cons element elements ih =>
      have nodupParts := List.nodup_cons.mp nodup
      rw [adjustValuesEvents_cons, eraseOperations_append]
      rw [show Interface.totalIncreases
            (eraseOperations
                (state.adjustValueEvents element (target element)) ++
              eraseOperations
                ((state.adjustValue element (target element))
                  |>.adjustValuesEvents target elements)) =
            Interface.totalIncreases
                (eraseOperations
                  (state.adjustValueEvents element (target element))) +
              Interface.totalIncreases
                (eraseOperations
                  ((state.adjustValue element (target element))
                    |>.adjustValuesEvents target elements)) by
          simp [Interface.totalIncreases]]
      change
        Interface.totalIncreases
              (eraseOperations
                (state.adjustValueEvents element (target element))) +
            Interface.totalIncreases
              (eraseOperations
                ((state.adjustValue element (target element))
                  |>.adjustValuesEvents target elements)) = 0
      have headZero := totalIncreases_adjustValueEvents_eq_zero_of_le
        state element (target element) (targetLe element (by simp))
      have tailZero := ih
        (state := state.adjustValue element (target element)) nodupParts.2
        (by
          intro candidate candidateMember
          rw [adjustValue_value_of_ne]
          · exact targetLe candidate (by simp [candidateMember])
          · intro equal
            subst candidate
            exact nodupParts.1 candidateMember)
      omega

end State

end Splay.Lazy
