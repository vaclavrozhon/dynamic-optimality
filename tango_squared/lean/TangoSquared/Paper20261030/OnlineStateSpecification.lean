import TangoSquared.Paper20261030.MaintainedBSTMetadata

/-! Prefix-consistent choice of the already proved physical request traces.
This is a noncomputable state specification, not the bounded local program:
its proof state still contains the full primary reference and component
table. It establishes that no future request is needed to select the next
valid physical transition. Local synthesis remains a separate obligation. -/

namespace TangoSquared.Paper20261030.OnlineSpecification

open ColoredStorage PreferredProjection Secondary SecondaryDecomposition LocalReferences

variable {α : Type*} [DecidableEq α] {h : Nat}

structure State (reference : DepthTree 0 h) (keyWord : List α) where
  memory : MemoryState α
  perfect : memory.primary.Perfect (h+1)
  components : Components α
  valid : Components.Valid (completedDepth reference) memory.primary perfect memory.preference components
  word : memory.primary.leaves = keyWord

def State.physical {reference : DepthTree 0 h} {keyWord : List α} (state : State reference keyWord) :=
  GapBST.Storage.encode (physicalState state.memory.primary state.components)

def key (keyWord : List α) (request : Fin keyWord.length) : α := keyWord[request]

def State.budget {reference : DepthTree 0 h} {keyWord : List α} (state : State reference keyWord)
    (request : Fin keyWord.length) : Nat :=
  7*((memoryCost (memoryKeys state.memory.primary reference) state.memory [key keyWord request] +
    state.memory.primary.accessFlips (key keyWord request)+1)*physicalRequestFactor reference)+3

structure Transition {reference : DepthTree 0 h} {keyWord : List α}
    (before : State reference keyWord) (request : Fin keyWord.length) where
  after : State reference keyWord
  memory : after.memory = before.memory.completeAdvance (h+1) (key keyWord request)
  cost : Nat
  execution : Auxiliary.Metadata.Access (key keyWord request) before.physical after.physical cost
  bound : cost ≤ before.budget request

theorem transition_exists {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) (request : Fin keyWord.length) :
    Nonempty (Transition state request) := by
  have member : key keyWord request ∈ state.memory.primary.leaves := by
    rw [state.word]
    exact List.getElem_mem _
  have nodup : state.memory.primary.leaves.Nodup := state.word.symm ▸ distinct
  obtain ⟨out,valid,visit⟩ := maintained_physical_request reference state.memory state.perfect nodup
    (key keyWord request) member state.components state.valid
  let after : State reference keyWord := {
    memory := state.memory.completeAdvance (h+1) (key keyWord request)
    perfect := PrefRouter.perfect_access state.perfect _
    components := out
    valid := valid
    word := (PrefRouter.access_leaves _ _).trans state.word }
  obtain ⟨cost,execution,bound⟩ := GapBST.Storage.visitsLeaf visit
  exact ⟨⟨after,rfl,cost,execution,bound⟩⟩

noncomputable def step {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) (request : Fin keyWord.length) :
    Transition state request := Classical.choice (transition_exists distinct state request)

noncomputable def run {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) : List (Fin keyWord.length) → State reference keyWord × Nat
  | [] => (state,0)
  | request::requests =>
      let first := step distinct state request
      let last := run distinct first.after requests
      (last.1,first.cost+last.2)

theorem run_execution {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) (requests : List (Fin keyWord.length)) :
    Auxiliary.Metadata.Execution state.physical (requests.map (key keyWord))
      (run distinct state requests).1.physical (run distinct state requests).2 := by
  induction requests generalizing state with
  | nil => exact .nil _
  | cons request requests ih => exact .cons (step distinct state request).execution (ih _)

theorem run_memory {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) (requests : List (Fin keyWord.length)) :
    (run distinct state requests).1.memory = completeRun (h+1) state.memory (requests.map (key keyWord)) := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih =>
    change (run distinct (step distinct state request).after requests).1.memory = _
    rw [ih,(step distinct state request).memory]
    rfl

/-- Extending the request word continues from the exact previously chosen
state and adds the continuation's cost. Choices for the prefix are fixed. -/
theorem run_append {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord)
    (first last : List (Fin keyWord.length)) :
    run distinct state (first++last) =
      let front := run distinct state first
      let back := run distinct front.1 last
      (back.1,front.2+back.2) := by
  induction first generalizing state with
  | nil => simp [run]
  | cons request first ih =>
    simp only [List.cons_append,run,ih,Nat.add_assoc]

end TangoSquared.Paper20261030.OnlineSpecification
