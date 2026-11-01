import TangoSquared.Paper20261030.GapSourceCompilerCorrectness
import DynamicOptimality.LocalProgramSize

/-! Only the actual component ports need entry markers. Extending the
proof-level port function outside its used index range changes no stored
node. This removes the global marker premise from root-returning compiled
programs on finite auxiliary components. -/

namespace TangoSquared.Paper20261030.GapSource

open MTR ColoredStorage DynamicOptimality

namespace Controller

open Auxiliary SourceLocalProgram

variable {α κ ρ σ : Type*}

def completePorts (ports : Nat → Source α (MarkedRecord κ ρ)) (base count i : Nat) : Source α (MarkedRecord κ ρ) :=
  if base ≤ i ∧ i ≤ base+count then ports i else ports base

theorem completePorts_marked (ports : Nat → Source α (MarkedRecord κ ρ)) (base count : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base+count → boundary (ports i).rootRecord = true) (i : Nat) :
    boundary (completePorts ports base count i).rootRecord = true := by
  unfold completePorts
  split
  · rename_i bounds
    exact marked i bounds.1 bounds.2
  · exact marked base le_rfl (by omega)

theorem encoded_root (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat) (tree : RawTree (Record κ ρ)) :
    encodedCursor ports base (.atRoot tree) = ⟨GapSource.encode (Relabel.tree mark tree) ports base,[]⟩ := by
  simp only [encodedCursor,Relabel.cursor,Pointer.Cursor.atRoot,List.map_nil,GapSource.cursor,
    PointerGraft.offset,GapSource.frames,Nat.add_zero]

theorem completePorts_encode (ports : Nat → Source α (MarkedRecord κ ρ)) (base count : Nat)
    (tree : RawTree (Record κ ρ)) (size : tree.size = count) :
    GapSource.encode (Relabel.tree mark tree) (completePorts ports base count) base =
      GapSource.encode (Relabel.tree mark tree) ports base := by
  apply encode_congr
  intro i lower upper
  simp only [Relabel.tree_size,size] at upper
  exact if_pos ⟨lower,upper⟩

theorem compile_root_run {source : LocalProgram.Program σ κ ρ} {state last : σ}
    {before after : RawTree (Record κ ρ)} {observations budget}
    (run : LocalProgram.Run source state (.atRoot before) last (.atRoot after) observations budget)
    (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base+before.size → boundary (ports i).rootRecord = true) :
    ∃ reads cost, Run (code source) (.ready state)
      ⟨GapSource.encode (Relabel.tree mark before) ports base,[]⟩ (.ready last)
      ⟨GapSource.encode (Relabel.tree mark after) ports base,[]⟩ reads cost ∧ cost ≤ 7*budget := by
  have size := LocalProgram.metadata_trace_size run.trace
  change before.size = after.size at size
  obtain ⟨reads,cost,compiled,bound⟩ := compile_run run (completePorts ports base before.size)
    (completePorts_marked ports base before.size marked) base
  rw [encoded_root,encoded_root,completePorts_encode ports base before.size before rfl,
    completePorts_encode ports base before.size after size.symm] at compiled
  exact ⟨reads,cost,compiled,bound⟩

def ReadState.extraRecords : ReadState κ ρ → Nat
  | .start => 0
  | _ => 1

def WriteState.extraRecords : WriteState κ ρ → Nat
  | .start (.size _) | .done => 0
  | _ => 1

def State.extraRecords : State σ κ ρ → Nat
  | .ready _ | .error => 0
  | .reading _ phase => phase.extraRecords
  | .writing _ phase => phase.extraRecords

theorem extra_records (state : State σ κ ρ) : state.extraRecords ≤ 1 := by
  cases state with
  | ready | error => exact Nat.zero_le _
  | reading state phase => cases phase <;> simp [State.extraRecords,ReadState.extraRecords]
  | writing state phase => cases phase with
    | start operation => cases operation <;> simp [State.extraRecords,WriteState.extraRecords]
    | write => exact le_rfl
    | done => exact Nat.zero_le _

end Controller
end TangoSquared.Paper20261030.GapSource
