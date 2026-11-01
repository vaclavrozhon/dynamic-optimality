import VirtualNumericInsertion

namespace Splay.Research.VirtualPrefixInsertion

open Splay.Interface Splay.Research.VirtualInterfaceAdmin Splay.Research.VirtualNumericInsertion

def insertState {n : ℕ} (before : State n) (id : BlockId) (element : Element n) : State n :=
  ⟨before.blocks.modify id (fun block => { block with elements := element :: block.elements }),
    before.value⟩

theorem inserted_elements_perm {n : ℕ} (blocks : List (Block n))
    (id : BlockId) (source : Block n) (element : Element n)
    (found : blocks[id]? = some source) :
    ((blocks.modify id (fun block => { block with elements := element :: block.elements })).flatMap
      Block.elements).Perm (element :: blocks.flatMap Block.elements) := by
  induction blocks generalizing id with
  | nil => simp at found
  | cons head blocks ih =>
      cases id with
      | zero => simp
      | succ id =>
          simp only [List.getElem?_cons_succ] at found
          have tail := (ih id found).append_left head.elements
          simpa only [List.modify_succ_cons, List.flatMap_cons] using
            tail.trans (List.perm_middle.trans (List.Perm.refl _))

theorem growingCount_eq {n : ℕ} (before : State n)
    (id : BlockId) (element creator : Element n) :
    (insertState before id element).growingCount creator = before.growingCount creator := by
  unfold insertState State.growingCount
  induction before.blocks generalizing id with
  | nil => simp
  | cons head blocks ih =>
      cases id with
      | zero => simp only [List.modify_zero_cons, List.filter_cons]; split <;> rfl
      | succ id => simp only [List.modify_succ_cons, List.filter_cons]; split <;> simp_all

theorem insertState_valid {n : ℕ} {params : Parameters} (before : State n)
    (id : BlockId) (source : Block n) (element : Element n)
    (valid : before.Valid params) (found : before.blocks[id]? = some source)
    (fresh : element ∉ before.allElements) : (insertState before id element).Valid params := by
  refine ⟨?_, valid.2.1, ?_⟩
  · exact (inserted_elements_perm before.blocks id source element found).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨fresh, valid.1⟩)
  · intro creator
    rw [growingCount_eq]
    exact valid.2.2 creator

def peak {n : ℕ} (before : State n) (creator element : Element n) (target : ℕ) : ℕ :=
  max (max target (before.value creator+1)) (before.value element)

def events {n : ℕ} (before : State n) (id : BlockId)
    (creator element : Element n) (target : ℕ) : List (Operation n) :=
  List.replicate (peak before creator element target-before.value element)
    (.valueChange element .increase) ++ [.insert id element] ++
  List.replicate (peak before creator element target-target) (.valueChange element .decrease)

/-- Insert into an existing growing prefix, keeping every other value and
every block identity. There is no new block and the only excursion is the
minimum one enforcing the actual creator's strict order. -/
theorem realize {n : ℕ} {params : Parameters} (before : State n)
    (id : BlockId) (source : Block n) (element : Element n) (target : ℕ)
    (valid : before.Valid params) (found : before.blocks[id]? = some source)
    (growing : source.mode = .growing) (fresh : element ∉ before.allElements)
    (different : source.creator ≠ element)
    (positive : 1 ≤ target) (bounded : target ≤ params.valueBound)
    (creatorRoom : before.value source.creator+1 ≤ params.valueBound) :
    Trace params before (events before id source.creator element target)
      (insertState (setValue before element target) id element) := by
  let top := peak before source.creator element target
  have oldLe : before.value element ≤ top := le_max_right _ _
  have targetLe : target ≤ top := (le_max_left _ _).trans (le_max_left _ _)
  have creatorLe : before.value source.creator+1 ≤ top :=
    (le_max_right _ _).trans (le_max_left _ _)
  have topBound : top ≤ params.valueBound :=
    max_le (max_le bounded creatorRoom) (valid.2.1 element).2
  let raised := setValue before element top
  have raisedValid : raised.Valid params := setValue_valid before element top valid (by omega) topBound
  have raiseTrace : Trace params before
      (List.replicate (top-before.value element) (.valueChange element .increase)) raised := by
    have equal : before.value element + (top-before.value element) = top := by omega
    simpa [equal, raised] using increases_trace before element (top-before.value element) valid
      (by omega)
  have insertedValid := insertState_valid raised id source element raisedValid found fresh
  have insertStep : Step params raised (.insert id element) (insertState raised id element) := by
    refine ⟨raisedValid, .insert found growing fresh ?_ rfl rfl, insertedValid⟩
    simpa [raised, setValue, different] using creatorLe
  have lowerTrace := decreases_trace (insertState raised id element) element (top-target)
    insertedValid (by simp [insertState, raised, setValue]; omega)
  have endpoint : setValue (insertState raised id element) element
      ((insertState raised id element).value element-(top-target)) =
      insertState (setValue before element target) id element := by
    have arithmetic : top-(top-target) = target := by omega
    simp [insertState, raised, setValue, arithmetic]
  rw [endpoint] at lowerTrace
  exact trace_append (trace_append raiseTrace (.cons insertStep (.nil insertedValid))) lowerTrace

theorem increases_eq {n : ℕ} (before : State n) (id : BlockId)
    (creator element : Element n) (target : ℕ) :
    totalIncreases (events before id creator element target) =
      peak before creator element target-before.value element := by
  simp [events, totalIncreases, Operation.increaseCount]

theorem growth_eq_zero {n : ℕ} (before : State n) (id : BlockId)
    (creator element : Element n) (target : ℕ) :
    totalBlockGrowth (events before id creator element target) = 0 := by
  simp [events, totalBlockGrowth, Operation.blockGrowth]

theorem inserts_eq_one {n : ℕ} (before : State n) (id : BlockId)
    (creator element : Element n) (target : ℕ) :
    totalInserts (events before id creator element target) = 1 := by
  simp [events, totalInserts, Operation.insertCount]

end Splay.Research.VirtualPrefixInsertion

#print axioms Splay.Research.VirtualPrefixInsertion.realize
#print axioms Splay.Research.VirtualPrefixInsertion.increases_eq
#print axioms Splay.Research.VirtualPrefixInsertion.growth_eq_zero
