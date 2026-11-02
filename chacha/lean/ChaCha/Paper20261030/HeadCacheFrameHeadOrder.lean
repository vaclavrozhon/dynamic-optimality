import ChaCha.Paper20261030.LocalHeadReassembleRepack
import ChaCha.Paper20261030.SourceInorderLabels

set_option autoImplicit false

/-! Exact physical inorder preservation through head reassembly.
Staging and repacking keep the complete labelled tree; the immutable
source interpreter keeps the reached label at every application write.
-/

namespace ChaCha.Paper20261030.HeadCacheFrameHeadOrder

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ ι σ : Type*}

theorem source_run_deterministic {source : Program σ ρ} {state firstLast secondLast : σ}
    {before firstAfter secondAfter : Cursor α ρ} {firstReads secondReads firstCost secondCost}
    (first : Run source state before firstLast firstAfter firstReads firstCost)
    (second : Run source state before secondLast secondAfter secondReads secondCost) :
    firstLast = secondLast ∧ firstAfter = secondAfter ∧ firstReads = secondReads ∧ firstCost = secondCost := by
  induction first generalizing secondLast secondAfter secondReads secondCost with
  | halt stopped => cases second with
    | halt => exact ⟨rfl,rfl,rfl,rfl⟩
    | next step rest => exact False.elim (step.not_halted stopped)
  | next step rest ih => cases second with
    | halt stopped => exact False.elim (step.not_halted stopped)
    | next other tail =>
      obtain ⟨sameState,sameCursor,sameRead⟩ := step.deterministic other
      cases sameState
      cases sameCursor
      cases sameRead
      obtain ⟨lastEq,afterEq,readsEq,costEq⟩ := ih tail
      exact ⟨lastEq,afterEq,congrArg _ readsEq,congrArg (·+1) costEq⟩

theorem immutable_step_order {source : Program σ ρ} {state next : ImmutableSource.State σ ρ ι}
    {before after : Cursor α (ι × ρ)} {entry}
    (step : Step (ImmutableSource.program source) state before next after entry)
    (valid : ImmutableSource.Valid state before) :
    ImmutableSource.Valid next after ∧ after.tree.inorderLabels Prod.fst = before.tree.inorderLabels Prod.fst := by
  cases step with
  | read instruction => exact ⟨ImmutableSource.read_valid source state _ instruction before,rfl⟩
  | nav instruction moved => exact ⟨ImmutableSource.nav_valid source state next _ instruction after,
      (navigate_inorderLabels Prod.fst _ moved).symm⟩
  | write instruction =>
    cases state with
    | ready state => cases h : source state <;> simp_all [ImmutableSource.program]
    | writing ident fresh next =>
      simp only [ImmutableSource.program,Instruction.write.injEq] at instruction
      obtain ⟨rfl,rfl⟩ := instruction
      exact ⟨trivial,plug_inorderLabels_congr Prod.fst
        (Source.inorderLabels_setRoot Prod.fst before.focus (ident,fresh) valid) before.ancestors⟩

theorem immutable_run_order {source : Program σ ρ} {state last : ImmutableSource.State σ ρ ι}
    {before after : Cursor α (ι × ρ)} {reads cost}
    (run : Run (ImmutableSource.program source) state before last after reads cost)
    (valid : ImmutableSource.Valid state before) :
    after.tree.inorderLabels Prod.fst = before.tree.inorderLabels Prod.fst := by
  induction run with
  | halt => rfl
  | next first rest ih =>
    obtain ⟨middleValid,firstOrder⟩ := immutable_step_order first valid
    exact (ih middleValid).trans firstOrder

theorem order_of_identifier_tree {α ρ τ ι : Type*} (first : ρ → ι) (second : τ → ι)
    (before : Source α ρ) (after : Source α τ)
    (same : after.mapRecords second = before.mapRecords first) :
    after.inorderLabels second = before.inorderLabels first := by
  have equal := congrArg (Source.inorderLabels id) same
  simpa only [Source.inorderLabels_map,Function.comp_def,id_eq] using equal

end ChaCha.Paper20261030.HeadCacheFrameHeadOrder

namespace ChaCha.Paper20261030.HeadReassembleRepack

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers
open PacketAlignment HeadBoundary HeadCacheFrameHeadOrder

variable {α β ρ ι η : Type*}

theorem order_of_run (markerId : ι) (direction : Bool) (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : Neutral markerId newHeader) (dormantValid : Neutral markerId dormantHeader)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (ordinary : HeadPacketLayout.WingRoots markerId (ObservedHeadBlueprint.bits old) blocks)
    (layout : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some layout)
    (initial : Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (initialView : OrderedContext.decorated
      (fun key => if ObservedHeadBlueprint.bits old key then some (blocks key) else none)
      (ObservedHeadBlueprint.beforeContext (markerValue markerId) direction old oldHeader incomingHeader) = some initial)
    (outside) (current : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (erases : current.mapRecords Prod.snd = ⟨initial,outside⟩)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) current.tree)
    {target : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)} {reads cost}
    (actual : Run (program (PacketLayers.Context.commands (layout.mapRecords blueprint)))
      (.inl (.ready (.ready (OrderedContext.Local.decoratedActions (ObservedHeadBlueprint.bits old)
        (ObservedHeadBlueprint.beforeContext (markerValue markerId) direction old oldHeader incomingHeader)
        (ObservedHeadBlueprint.afterContext (markerValue markerId) direction fresh newHeader dormantHeader))))) current
      (.inr (.running [])) target reads cost) :
    target.tree.inorderLabels Prod.fst = current.tree.inorderLabels Prod.fst := by
  have finalView := HeadPacketLayout.after_realizes markerId (ObservedHeadBlueprint.bits old) direction fresh
    newHeader dormantHeader rfl rfl layout found blocks
  let finalTree := Reached.stagedTree markerId blocks layout
  have finalEq : OrderedContext.decorated
      (fun key => if ObservedHeadBlueprint.bits old key then some (blocks key) else none)
      (ObservedHeadBlueprint.afterContext (markerValue markerId) direction fresh newHeader dormantHeader) = some finalTree :=
    finalView.symm
  have presence (key : Fin 8) :
      (if ObservedHeadBlueprint.bits old key then some (blocks key) else none).isSome = ObservedHeadBlueprint.bits old key := by
    cases ObservedHeadBlueprint.bits old key <;> rfl
  obtain ⟨middle,frontReads,frontCost,frontRun,middleErases,_,middleAligned,_⟩ :=
    PacketAlignment.reassemble markerId _ _ _
      (ObservedHeadBlueprint.block_order (markerValue markerId) direction old fresh oldHeader incomingHeader newHeader dormantHeader)
      (PacketAlignment.after_neutral markerId direction fresh newHeader dormantHeader newValid dormantValid)
      initial finalTree initialView finalEq outside current erases aligned
  simp only [presence] at frontRun
  have frontOrder := immutable_run_order frontRun trivial
  have focusedEq := congrArg Cursor.focus middleErases
  change middle.focus.mapRecords Prod.snd = finalTree at focusedEq
  have focusedValid : SourceRecordPredicate.Holds (Predicate markerId) middle.focus := by
    intro record member
    exact middleAligned record (Multiset.mem_of_le (inventory_le_plug id middle.focus middle.ancestors) member)
  obtain ⟨last,backRun,_,lastIds,_⟩ := Reached.repack markerId blocks layout
    (HeadPacketLayout.after_good markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader blocks ordinary layout found)
    middle.focus focusedEq focusedValid
  obtain ⟨backReads,backRun⟩ := backRun middle.ancestors
  have positive : 0 < PhysicalPacketStaging.Context.budget layout := by
    cases layout <;> simp only [PhysicalPacketStaging.Context.budget] <;> omega
  have checked := Sequential.run frontRun (by rfl) backRun positive (by rfl)
  have same := source_run_deterministic checked actual
  rw [← same.2.1]
  exact (plug_inorderLabels_congr Prod.fst
    (order_of_identifier_tree Prod.fst Prod.fst middle.focus last lastIds) middle.ancestors).trans frontOrder

end ChaCha.Paper20261030.HeadReassembleRepack
