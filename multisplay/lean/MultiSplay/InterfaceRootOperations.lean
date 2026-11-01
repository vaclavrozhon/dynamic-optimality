import MultiSplay.InterfaceExcess
import Splay.Interface.OperationCounts

/-!
# Actual interface operations at common root joins and splits

Old blocks and their pass counters persist. Attaching a component root creates
one fresh singleton at the new pivot, with a single paid value increase from
one to two. Detachment converts the singleton if necessary, deletes its member,
and explicitly restores the member's neutral value. In particular, `Convert`
itself is never treated as a value change.
-/

namespace MultiSplay.InterfaceForest

open Splay.Interface

variable {n : Nat}

def setValue (state : State n) (element : Element n) (value : Nat) : State n :=
  ⟨state.blocks, Function.update state.value element value⟩

theorem setValue_valid {params : Parameters} (state : State n) (element : Element n) (value : Nat)
    (valid : state.Valid params) (bounds : 1 ≤ value ∧ value ≤ params.valueBound) :
    (setValue state element value).Valid params := by
  refine ⟨valid.1, ?_, valid.2.2⟩
  intro queried
  by_cases same : queried = element
  · simpa [setValue, same] using bounds
  · simpa [setValue, Function.update_of_ne same] using valid.2.1 queried

theorem increase_step {params : Parameters} (state : State n) (element : Element n)
    (valid : state.Valid params) (room : state.value element < params.valueBound) :
    Step params state (.valueChange element .increase)
      (setValue state element (state.value element + 1)) := by
  exact ⟨valid, .increase room rfl rfl, setValue_valid state element _ valid ⟨by omega, by omega⟩⟩

theorem decrease_step {params : Parameters} (state : State n) (element : Element n)
    (valid : state.Valid params) (positive : 1 < state.value element) :
    Step params state (.valueChange element .decrease)
      (setValue state element (state.value element - 1)) := by
  have bound := (valid.2.1 element).2
  exact ⟨valid, .decrease positive rfl rfl,
    setValue_valid state element _ valid ⟨by omega, by omega⟩⟩

def rootBlock (pivot : Element n) (elements : List (Element n)) : Block n :=
  ⟨pivot, 0, .growing, elements⟩

def appendBlock (state : State n) (block : Block n) : State n :=
  ⟨state.blocks ++ [block], state.value⟩

theorem appendBlock_elements (state : State n) (block : Block n) :
    (appendBlock state block).allElements = state.allElements ++ block.elements := by
  simp [appendBlock, State.allElements]

theorem appendBlock_growingCount (state : State n) (pivot queried : Element n)
    (elements : List (Element n)) :
    (appendBlock state (rootBlock pivot elements)).growingCount queried =
      state.growingCount queried + if pivot = queried then 1 else 0 := by
  by_cases same : pivot = queried <;> simp [appendBlock, rootBlock, State.growingCount, same]

theorem append_rootBlock_valid {params : Parameters} (state : State n) (pivot : Element n)
    (elements : List (Element n)) (valid : state.Valid params)
    (distinct : (state.allElements ++ elements).Nodup)
    (room : state.growingCount pivot < params.growingLimit) :
    (appendBlock state (rootBlock pivot elements)).Valid params := by
  refine ⟨?_, valid.2.1, ?_⟩
  · simpa [appendBlock_elements, rootBlock] using distinct
  · intro queried
    rw [appendBlock_growingCount]
    by_cases same : pivot = queried
    · subst queried; simpa using room
    · simpa [same] using valid.2.2 queried

theorem create_step {params : Parameters} (state : State n) (pivot : Element n)
    (valid : state.Valid params) (room : state.growingCount pivot < params.growingLimit) :
    Step params state (.create pivot) (appendBlock state (rootBlock pivot [])) := by
  refine ⟨valid, .create room rfl rfl, ?_⟩
  exact append_rootBlock_valid state pivot [] valid (by simpa using valid.1) room

private theorem modify_last {α : Type*} (blocks : List α) (last : α) (f : α → α) :
    (blocks ++ [last]).modify blocks.length f = blocks ++ [f last] := by
  induction blocks <;> simp_all

theorem insert_fresh_step {params : Parameters} (state : State n) (pivot child : Element n)
    (valid : state.Valid params) (room : state.growingCount pivot < params.growingLimit)
    (unassigned : child ∉ state.allElements)
    (valueOrder : state.value pivot + 1 ≤ state.value child) :
    Step params (appendBlock state (rootBlock pivot []))
      (.insert state.blocks.length child) (appendBlock state (rootBlock pivot [child])) := by
  have emptyValid := (create_step state pivot valid room).2.2
  refine ⟨emptyValid, ?_, ?_⟩
  · apply Effect.insert (block := rootBlock pivot [])
    · simp [State.block?, appendBlock]
    · rfl
    · simpa [appendBlock_elements, rootBlock] using unassigned
    · exact valueOrder
    · simpa [appendBlock, rootBlock] using
        (modify_last state.blocks (rootBlock pivot [])
          (fun current => { current with elements := child :: current.elements })).symm
    · rfl
  · apply append_rootBlock_valid state pivot [child] valid ?_ room
    simpa using valid.1.concat unassigned

def attach (state : State n) (pivot child : Element n) : State n :=
  appendBlock (setValue state child 2) (rootBlock pivot [child])

def attachWord (state : State n) (pivot child : Element n) : List (Operation n) :=
  [.valueChange child .increase, .create pivot, .insert state.blocks.length child]

/-- Construction from an arbitrary current state: the old prefix of blocks
is retained literally, including creators, element order, and pass counts. -/
theorem attach_trace {params : Parameters} (state : State n) (pivot child : Element n)
    (valid : state.Valid params) (different : child ≠ pivot)
    (pivotOne : state.value pivot = 1) (childOne : state.value child = 1)
    (unassigned : child ∉ state.allElements)
    (room : state.growingCount pivot < params.growingLimit) :
    Trace params state (attachWord state pivot child) (attach state pivot child) := by
  have first : Step params state (.valueChange child .increase) (setValue state child 2) := by
    simpa [childOne] using increase_step state child valid (by rw [childOne]; exact params.valueBound_ge_two)
  have nextValid := first.2.2
  have second := create_step (setValue state child 2) pivot nextValid room
  have valueOrder : (setValue state child 2).value pivot + 1 ≤
      (setValue state child 2).value child := by simp [setValue, Ne.symm different, pivotOne]
  have third := insert_fresh_step (setValue state child 2) pivot child nextValid room unassigned valueOrder
  exact .cons first (.cons second (.cons third (.nil third.2.2)))

@[simp] theorem attach_blocks (state : State n) (pivot child : Element n) :
    (attach state pivot child).blocks = state.blocks ++ [rootBlock pivot [child]] := rfl

@[simp] theorem attachWord_inserts (state : State n) (pivot child : Element n) :
    totalInserts (attachWord state pivot child) = 1 := rfl

@[simp] theorem attachWord_increases (state : State n) (pivot child : Element n) :
    totalIncreases (attachWord state pivot child) = 1 := rfl

@[simp] theorem attachWord_activity (state : State n) (pivot child : Element n) :
    totalActivity (attachWord state pivot child) = 0 := rfl

theorem trace_append {params : Parameters} {a b c : State n}
    {first rest : List (Operation n)} (run₁ : Trace params a first b) (run₂ : Trace params b rest c) :
    Trace params a (first ++ rest) c := by
  induction run₁ with
  | nil => exact run₂
  | cons head tail ih => exact .cons head (ih run₂)

def join (state : State n) (pivot left right : Element n) : State n :=
  attach (attach state pivot left) pivot right

def joinWord (state : State n) (pivot left right : Element n) : List (Operation n) :=
  attachWord state pivot left ++ attachWord (attach state pivot left) pivot right

/-- A full common root join uses two existing child roots. Its six legal
primitive operations append two records and preserve every previous block. -/
theorem join_trace {params : Parameters} (state : State n) (pivot left right : Element n)
    (valid : state.Valid params) (leftNe : left ≠ pivot) (rightNe : right ≠ pivot)
    (childrenNe : right ≠ left)
    (pivotOne : state.value pivot = 1) (leftOne : state.value left = 1) (rightOne : state.value right = 1)
    (leftFree : left ∉ state.allElements) (rightFree : right ∉ state.allElements)
    (room : state.growingCount pivot + 2 ≤ params.growingLimit) :
    Trace params state (joinWord state pivot left right) (join state pivot left right) := by
  have first := attach_trace state pivot left valid leftNe pivotOne leftOne leftFree (by omega)
  have middleValid := trace_final_valid first
  have pivotMiddle : (attach state pivot left).value pivot = 1 := by
    simp [attach, appendBlock, setValue, Ne.symm leftNe, pivotOne]
  have rightMiddle : (attach state pivot left).value right = 1 := by
    simp [attach, appendBlock, setValue, childrenNe, rightOne]
  have rightUnassigned : right ∉ (attach state pivot left).allElements := by
    rw [attach, appendBlock_elements]
    change right ∉ state.allElements ++ [left]
    simp [rightFree, childrenNe]
  have roomMiddle : (attach state pivot left).growingCount pivot < params.growingLimit := by
    simp only [attach, appendBlock_growingCount, ite_true]
    change state.growingCount pivot + 1 < params.growingLimit
    omega
  exact trace_append first
    (attach_trace _ pivot right middleValid rightNe pivotMiddle rightMiddle rightUnassigned roomMiddle)

theorem join_blocks (state : State n) (pivot left right : Element n) :
    (join state pivot left right).blocks =
      state.blocks ++ [rootBlock pivot [left], rootBlock pivot [right]] := by
  simp [join, List.append_assoc]

theorem join_old_block (state : State n) (pivot left right : Element n) {id : Nat}
    (old : id < state.blocks.length) :
    (join state pivot left right).block? id = state.block? id := by
  simp [State.block?, join_blocks, List.getElem?_append_left old]

@[simp] theorem joinWord_inserts (state : State n) (pivot left right : Element n) :
    totalInserts (joinWord state pivot left right) = 2 := by simp [joinWord]

@[simp] theorem joinWord_increases (state : State n) (pivot left right : Element n) :
    totalIncreases (joinWord state pivot left right) = 2 := by simp [joinWord]

@[simp] theorem joinWord_activity (state : State n) (pivot left right : Element n) :
    totalActivity (joinWord state pivot left right) = 0 := by simp [joinWord]

end MultiSplay.InterfaceForest
