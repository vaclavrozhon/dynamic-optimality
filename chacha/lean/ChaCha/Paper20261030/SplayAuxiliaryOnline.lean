import ChaCha.Paper20261030.SplayAuxiliaryRequest
import ChaCha.Paper20261030.SplayAuxiliaryGlobalMass
import ChaCha.Paper20261030.OnlineStateAccounting

/-! A fixed online ordinary-splay Cha-Cha strategy. Classical choices use
only the maintained state and the current request. Each transition keeps
its actual splay transcript and charges the initial search and rotations. -/

namespace ChaCha.Paper20261030.SplayAuxiliary.Online

open DynamicOptimality.SearchRotation
open ColoredStorage PreferredProjection Secondary LocalReferences Rectangles

variable {α : Type*} [LinearOrder α] {h : Nat}

abbrev State (reference : DepthTree 0 h) (keyWord : List α) := Global.State (completedDepth reference) keyWord

abbrev key (keyWord : List α) (request : Fin keyWord.length) : α := OnlineSpecification.key keyWord request

def accessFactor (reference : DepthTree 0 h) : Nat := 2*requestFactor reference+2

def tree {reference : DepthTree 0 h} {keyWord : List α} (state : State reference keyWord) :=
  GapBST.encode (Physical.physicalState state.memory.primary state.components)

def potential {reference : DepthTree 0 h} {keyWord : List α} (state : State reference keyWord) : Nat :=
  state.components.potential keyWord.toFinset

theorem tree_word {reference : DepthTree 0 h} {keyWord : List α}
    (ordered : keyWord.Pairwise (· < ·)) (state : State reference keyWord) :
    (tree state).inorder = keyWord := by
  have distinct : state.memory.primary.leaves.Nodup := state.word.symm ▸ ordered.imp (fun smaller => ne_of_lt smaller)
  rw [tree,GapBST.encode_word,Physical.physical_leaves _ state.perfect distinct _ _ state.valid,state.word]

structure Transition {reference : DepthTree 0 h} {keyWord : List α}
    (before : State reference keyWord) (request : Fin keyWord.length) where
  after : State reference keyWord
  memory : after.memory = before.memory.completeAdvance (h+1) (key keyWord request)
  cost : Nat
  execution : Access (key keyWord request) (tree before) (tree after) cost
  ordinary : RequestExecution reference before.memory (key keyWord request) before.components after.components
  bound : cost+816*potential after ≤ 816*potential before+
    (memoryCost (memoryKeys before.memory.primary reference) before.memory [key keyWord request]+
      before.memory.primary.accessFlips (key keyWord request)+1)*accessFactor reference

 theorem transition_exists {reference : DepthTree 0 h} {keyWord : List α}
    (ordered : keyWord.Pairwise (· < ·)) (state : State reference keyWord) (request : Fin keyWord.length) :
    Nonempty (Transition state request) := by
  have member : key keyWord request ∈ state.memory.primary.leaves := by rw [state.word]; exact List.getElem_mem _
  have primaryOrdered : state.memory.primary.leaves.Pairwise (· < ·) := state.word.symm ▸ ordered
  obtain ⟨out,cost,valid,execution,ordinary,bound⟩ := request_access reference state.memory
    (key keyWord request) state.perfect primaryOrdered member state.components state.valid
  let after : State reference keyWord := {
    memory := state.memory.completeAdvance (h+1) (key keyWord request)
    perfect := PrefRouter.perfect_access state.perfect _
    components := out
    valid := valid
    word := (PrefRouter.access_leaves _ _).trans state.word }
  refine ⟨⟨after,rfl,cost,execution,ordinary,?_⟩⟩
  simpa only [potential,after,PrefRouter.access_leaves,state.word,accessFactor] using bound

noncomputable def step {reference : DepthTree 0 h} {keyWord : List α}
    (ordered : keyWord.Pairwise (· < ·)) (state : State reference keyWord) (request : Fin keyWord.length) :
    Transition state request := Classical.choice (transition_exists ordered state request)

noncomputable def run {reference : DepthTree 0 h} {keyWord : List α}
    (ordered : keyWord.Pairwise (· < ·)) (state : State reference keyWord) :
    List (Fin keyWord.length) → State reference keyWord × Nat
  | [] => (state,0)
  | request::requests =>
    let first := step ordered state request
    let last := run ordered first.after requests
    (last.1,first.cost+last.2)

 theorem run_execution {reference : DepthTree 0 h} {keyWord : List α}
    (ordered : keyWord.Pairwise (· < ·)) (state : State reference keyWord) (requests : List (Fin keyWord.length)) :
    Execution (tree state) (requests.map (key keyWord))
      (tree (run ordered state requests).1) (run ordered state requests).2 := by
  induction requests generalizing state with
  | nil => exact .nil _
  | cons request requests ih => exact .cons (step ordered state request).execution (ih _)

 theorem run_append {reference : DepthTree 0 h} {keyWord : List α}
    (ordered : keyWord.Pairwise (· < ·)) (state : State reference keyWord)
    (first last : List (Fin keyWord.length)) :
    run ordered state (first++last) =
      let front := run ordered state first
      let back := run ordered front.1 last
      (back.1,front.2+back.2) := by
  induction first generalizing state with
  | nil => simp [run]
  | cons request first ih => simp only [List.cons_append,run,ih,Nat.add_assoc]

 theorem run_cost {reference : DepthTree 0 h} {keyWord : List α}
    (ordered : keyWord.Pairwise (· < ·)) (state : State reference keyWord) (requests : List (Fin keyWord.length)) :
    (run ordered state requests).2+816*potential (run ordered state requests).1 ≤
      816*potential state+
      (memoryCost (memoryKeys state.memory.primary reference) state.memory (requests.map (key keyWord))+
        state.memory.primary.runFlips (requests.map (key keyWord))+requests.length)*accessFactor reference := by
  induction requests generalizing state with
  | nil => simp [run,memoryCost,PrefRouter.runFlips]
  | cons request requests ih =>
    have first := (step ordered state request).bound
    have last := ih (step ordered state request).after
    rw [(step ordered state request).memory] at last
    change (run ordered (step ordered state request).after requests).2+
        816*potential (run ordered (step ordered state request).after requests).1 ≤
      816*potential (step ordered state request).after+
      (memoryCost (memoryKeys (state.memory.primary.access (key keyWord request)) reference)
        (state.memory.completeAdvance (h+1) (key keyWord request)) (requests.map (key keyWord))+
        (state.memory.primary.access (key keyWord request)).runFlips (requests.map (key keyWord))+
        requests.length)*accessFactor reference at last
    rw [memoryKeys_access,completeAdvance_memoryCost] at last
    change (step ordered state request).cost+(run ordered (step ordered state request).after requests).2+
      816*potential (run ordered (step ordered state request).after requests).1 ≤ _
    simp only [memoryCost,List.map_cons,PrefRouter.runFlips,List.length_cons,
      Nat.add_zero,Nat.zero_add,Nat.mul_add,Nat.add_mul,Nat.one_mul] at first last ⊢
    omega

noncomputable def canonicalState (reference : DepthTree 0 h) : State reference (Dyadic.canonical (h+1) 0).leaves := {
  memory := MemoryState.initial (Dyadic.canonical (h+1) 0)
  perfect := Dyadic.canonical_perfect _ _
  components := Global.Table.initial (completedDepth reference) (Dyadic.canonical (h+1) 0)
    (Dyadic.canonical_perfect _ _) (fun _ => true)
  valid := Global.Table.initial_valid _ _ _ _
  word := rfl }

 theorem canonical_cost (reference : DepthTree 0 h)
    (requests : List (Fin (Dyadic.canonical (h+1) 0).leaves.length)) :
    (run (Dyadic.canonical_ordered _ _) (canonicalState reference) requests).2 ≤
      (requests.length+13*robustBound (accessPoints (requests.map (key (Dyadic.canonical (h+1) 0).leaves)))+
        8*2^(h+1))*accessFactor reference := by
  have bound := run_cost (Dyadic.canonical_ordered (h+1) 0) (canonicalState reference) requests
  have valid : ∀ x ∈ requests.map (key (Dyadic.canonical (h+1) 0).leaves), Dyadic.ValidKey (h+1) x := by
    intro x member
    obtain ⟨request,_,rfl⟩ := List.mem_map.mp member
    exact (Dyadic.canonical_zero_mem _ _).mp (List.getElem_mem _)
  have work := Dyadic.abstract_work_robust_bound reference _ valid
  simp only [Dyadic.abstractWork,PrefRouter.depthAccessCount_eq,secondaryCost,MemoryState.initial,List.length_map] at work
  have initialPotential := (canonicalState reference).valid.potential_bound (completedDepth reference)
    (Dyadic.canonical (h+1) 0) (Dyadic.canonical_perfect _ _) (Dyadic.canonical_nodup _ _) _ _
  have length : (Dyadic.canonical (h+1) 0).leaves.length = 2^(h+1) :=
    perfect_leaf_count (Dyadic.canonical_perfect _ _)
  rw [length] at initialPotential
  have reserve : 816*potential (canonicalState reference) ≤ 2*2^(h+1)*accessFactor reference := by
    change 816*(canonicalState reference).components.potential (Dyadic.canonical (h+1) 0).leaves.toFinset ≤ _
    unfold accessFactor requestFactor headFactor
    nlinarith
  have coefficient : memoryCost (memoryKeys (Dyadic.canonical (h+1) 0) reference)
      (MemoryState.initial (Dyadic.canonical (h+1) 0)) (requests.map (key (Dyadic.canonical (h+1) 0).leaves))+
      (Dyadic.canonical (h+1) 0).runFlips (requests.map (key (Dyadic.canonical (h+1) 0).leaves))+requests.length ≤
        requests.length+13*robustBound (accessPoints (requests.map (key (Dyadic.canonical (h+1) 0).leaves)))+6*2^(h+1) := by
    simpa only [MemoryState.initial] using (show _ ≤ _ by omega)
  have charged := Nat.mul_le_mul_right (accessFactor reference) coefficient
  change _ ≤ 816*potential (canonicalState reference)+_ at bound
  simp only [canonicalState,MemoryState.initial] at bound charged reserve ⊢
  nlinarith

end ChaCha.Paper20261030.SplayAuxiliary.Online
