import MultiSplay.SharedInitialization

/-! # Constructing the initial certified component without assumptions on a run -/

namespace MultiSplay

open Splay.Interface

theorem InterfaceFramedTrace.identity (params : Parameters) {n : Nat} (component : State n) :
    Nonempty (InterfaceFramedTrace.Framed params component component) := by
  let frame : State n := ⟨[], fun _ => 1⟩
  have mapped : component.blocks.map (InterfaceEmbedding.block id) = component.blocks := by
    have identity : InterfaceEmbedding.block (id : Element n → Element n) = id := by
      funext block
      cases block
      simp [InterfaceEmbedding.block]
    rw [identity, List.map_id]
  refine ⟨⟨id, Function.injective_id, frame, ?_, ?_, ?_⟩⟩
  · constructor <;> simp [frame, State.allElements]
  · refine ⟨by simp [frame, State.allElements], ?_, ?_⟩
    · intro x
      have cap := params.valueBound_ge_two
      change 1 ≤ 1 ∧ 1 ≤ params.valueBound
      omega
    · intro creator
      simp [frame, State.growingCount]
  · constructor
    · simpa only [InterfacePrefix.state, frame, List.nil_append, mapped] using List.Perm.refl (component.blocks.map InterfaceHistory.observable)
    · exact Function.extend_id _ _

namespace SharedSplay

open Splay.Accounting Splay.Rank Splay.Lazy.Canonical

variable {n : Nat} {params : Parameters}

theorem canonical_certified (comparison tree : Splay.Tree.BST 0 n)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound : Splay.Analysis.contractedGap (Snapshot.ofTree comparison).withTruePriority.maxRank ≤ params.valueBound) :
    Certified params ⟨comparison, tree, canonicalState (Snapshot.ofTree comparison).withTruePriority tree⟩ := by
  refine ⟨canonicalState_represents _ _ _ growingLimit valueBound, ?_, canonicalState_passedBlocksUnbroken _ _⟩
  rw [rich_growing_zero_iff]
  intro block member growing
  obtain ⟨placement, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- A one-component starting state, its real initialization, linear mass and
initial excess bound are all constructed. The same setup operation embeds in
an arbitrary passive forest through `setup_exists`. -/
theorem canonical_start (comparison tree : Splay.Tree.BST 0 n)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound : Splay.Analysis.contractedGap (Snapshot.ofTree comparison).withTruePriority.maxRank ≤ params.valueBound) :
    ∃ initial final : State n, ∃ setup : Initialization params initial final,
      initial.Initial params ∧ InterfaceForest.excess initial ≤ params.valueBound * (2*n+1) ∧
      setup.mass = 2*n+1 ∧
      Nonempty (InterfaceFramedTrace.Framed params (canonicalState (Snapshot.ofTree comparison).withTruePriority tree).toInterface final) ∧
      Certified params ⟨comparison, tree, canonicalState (Snapshot.ofTree comparison).withTruePriority tree⟩ := by
  let initial := (emptyCanonicalState (Snapshot.ofTree comparison).withTruePriority tree).toInterface
  obtain ⟨framed⟩ := InterfaceFramedTrace.identity params initial
  obtain ⟨setup⟩ := setup_exists (Snapshot.ofTree comparison).withTruePriority tree growingLimit valueBound initial framed
  have initialized := emptyCanonicalState_toInterface_initial (Snapshot.ofTree comparison).withTruePriority tree params valueBound
  have excess := InterfaceForest.excess_add_card initialized.1
  have values := Splay.Interface.State.totalValue_le initialized.1
  refine ⟨initial, setup.final, .next setup valueBound rfl (.done setup.final), initialized, ?_, by simp [Initialization.mass],
    ⟨setup.framed⟩, canonical_certified comparison tree growingLimit valueBound⟩
  nlinarith

end SharedSplay
end MultiSplay
