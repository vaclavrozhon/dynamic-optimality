import TangoSquared.Paper20261030.LocalComponentTerminalExposure
import TangoSquared.Paper20261030.ComponentVirtualRoot
import TangoSquared.Paper20261030.PrimaryRefreshingReentry
import TangoSquared.Paper20261030.ThreeColorLayoutStability
import TangoSquared.Paper20261030.ComponentOriginalKeys

/-! Actual original-key terminal exposure with retained root identity,
logical register masks, and final primary-header repair. The continuation
receives only the saved finite header/root/register context. The logical
tree, including identifiers, is unchanged; its reached exit payload is
exposed in the actual shared tree when this controller halts.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.CachedTerminalController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler ComponentTerminalController ForestConnector.ThreeColors

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

variable {β ι η : Type*} [DecidableEq ι] [DecidableEq η]

abbrev Record (ι η : Type*) := PrimaryHeaderController.Record (List (Option (Datum ι η (Option Bool)))) η
abbrev BodyState (ι η : Type*) := MultiSourceMask.State
  (MultiSourceAugment.State (ComponentTerminalController.ControllerState ι η (Option Bool)) (Option Bool)
    (List (Option (Datum ι η (Option Bool)))) (Option (PrimaryHeaderController.Header η))) (Option Bool)
abbrev ControllerState (ι η : Type*) := MultiSourceFinish.State (BodyState ι η)
  (PrimaryRefreshingReentry.RefreshState (Option (Datum ι η (Option Bool))) η) (PrimaryRefreshingReentry.Parameters η)

def body (height : Nat) (request : Int) (context : PrimaryRefreshingReentry.Context η) :
    MultiSourceProgram.Program (BodyState ι η) (Option Bool) (Record ι η) :=
  MultiSourceMask.program (MultiSourceAugment.program (ComponentTerminalController.program
    (Dyadic.computeExitDepth height request context.header.bottom) none LocalComponentCompiler.wingOrientation))

def select (context : PrimaryRefreshingReentry.Context η) (state : BodyState ι η) : PrimaryRefreshingReentry.Parameters η :=
  some {context with active := state.1}

def program (height : Nat) (request : Int) (context : PrimaryRefreshingReentry.Context η) :
    MultiSourceProgram.Program (ControllerState ι η) (Option Bool) (Record ι η) :=
  MultiSourceFinish.program (body height request context) (select context) PrimaryRefreshingReentry.initial PrimaryRefreshingReentry.target

def initial (height : Nat) (request : Int) (context : PrimaryRefreshingReentry.Context η) : ControllerState ι η :=
  MultiSourceFinish.enter (body height request context) (select context) PrimaryRefreshingReentry.initial
    (context.active,.ready (ComponentTerminalController.initial context.rootId))

theorem expose {a b H : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Int) (context : PrimaryRefreshingReentry.Context η)
    (validRequest : Dyadic.ValidKey H request) (validBottom : Dyadic.ValidKey H context.header.bottom)
    (terminal : (Secondary.decodeDepth reference preferences).terminal = Dyadic.lcaDepth H request context.header.bottom)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup) (rootId : context.rootId = decorated.rootRecord.1)
    (forest : TaggedForest (Option Bool) Nat (LogicalRecord η (Option Bool)) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (realColor : color (Dyadic.lcaDepth H request context.header.bottom) ≠ none)
    (headerKey : Nat) (payload : Option Bool → Nat → Source β (List (Option (Datum ι η (Option Bool)))))
    (leftWing : context.header.leftWing = (representation none LocalComponentCompiler.wingOrientation headerKey payload forest (some true)).isSome)
    (rightWing : context.header.rightWing = (representation none LocalComponentCompiler.wingOrientation headerKey payload forest (some false)).isSome)
    (config : MultiSourceProgram.Configuration (Option Bool) β (Record ι η))
    (validConfig : MultiSourceProgram.WellFormed config)
    (assembled : ForestConnector.assemble (representation none LocalComponentCompiler.wingOrientation headerKey payload forest)
      (layout (representation none LocalComponentCompiler.wingOrientation headerKey payload forest)) =
      some ((config.mask context.active).mapRecords Prod.fst)) :
    ∃ (target : Cursor Nat (η × Cached)), ∃ finalForest finalBits finalConfig reads cost,
      target.tree = decorated ∧
      MultiSourceProgram.Run (program H request context) (initial H request context) config
        (.second (some {context with active := finalBits}) (some .done)) finalConfig reads cost ∧
      ProjectionForest.Represents color (cursor Prod.fst color target) (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest)
        (layout (representation none LocalComponentCompiler.wingOrientation headerKey payload forest)) =
        some ((finalConfig.mask finalBits).mapRecords Prod.fst) ∧
      OriginalAccessController.Exposes finalConfig (color (Dyadic.lcaDepth H request context.header.bottom))
        (payload (color (Dyadic.lcaDepth H request context.header.bottom)) (Dyadic.lcaDepth H request context.header.bottom)) ∧
      finalConfig.tree.rootRecord.2 = some {context.header with rootId := context.rootId} ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 2*((59280*(Fintype.card (Option Bool)+1))*(6*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+1))+6 := by
  let physical := representation none LocalComponentCompiler.wingOrientation headerKey payload forest
  have depthEq : Dyadic.computeExitDepth H request context.header.bottom = Dyadic.lcaDepth H request context.header.bottom :=
    (Dyadic.computeExitDepth_correct validRequest validBottom).trans (Dyadic.exitDepth_eq_lcaDepth validRequest validBottom)
  obtain ⟨target,finalForest,plainFinal,plainReads,plainCost,sameTree,plainRun,finalRep,finalUnique,
      finalAssembled,finalCovered,plainValid,exposed,plainBound⟩ :=
    ComponentTerminalController.expose reference preferences (Dyadic.lcaDepth H request context.header.bottom) terminal component represented
      color decorated erases logicalUnique forest forestRep physicalUnique none realColor LocalComponentCompiler.wingOrientation
      headerKey payload (layout physical) (distinct physical) (covers physical) ((config.mask context.active).mapRecords Prod.fst) assembled
  rw [← rootId] at plainRun
  obtain ⟨logicalFinal,logicalReads,logicalCost,logicalRun,logicalErases,metadata,logicalBound⟩ :=
    MultiSourceAugment.compile_run plainRun (config.mask context.active) rfl
  obtain ⟨active,middle,middleReads,middleRun,middleErases,middleValid⟩ :=
    MultiSourceMask.compile_run logicalRun context.active config validConfig rfl
  have bodyRun : MultiSourceProgram.Run (body H request context)
      (context.active,.ready (ComponentTerminalController.initial context.rootId)) config
      (active,.ready (ComponentTerminalController.finalState target.focus.rootRecord.1)) middle middleReads logicalCost := by
    simpa only [body,depthEq] using middleRun
  have plainMiddle : (middle.mask active).mapRecords Prod.fst = plainFinal := by
    rw [middleErases]; exact logicalErases
  let finalPhysical := representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest
  obtain ⟨headerTree,headerPresent⟩ := LocalComponentCompiler.virtual_present_root none LocalComponentCompiler.wingOrientation headerKey payload finalForest
  obtain ⟨presence,canonical⟩ := canonical_final physical finalPhysical _ plainFinal assembled finalAssembled finalCovered headerTree headerPresent
  obtain ⟨final,refreshReads,refreshCost,refresh,finalErases,correctHeader,finalValid,refreshBound⟩ :=
    PrimaryHeaderRefresh.component_refresh context.header context.rootId finalPhysical headerTree
      (leftWing.trans (presence (some true)).symm) (rightWing.trans (presence (some false)).symm)
      active middle (plainMiddle.trans canonical) middleValid
  have back : MultiSourceProgram.Run (PrimaryRefreshingReentry.target
      (select (ι := ι) context (active,.ready (ComponentTerminalController.finalState target.focus.rootRecord.1))))
      (PrimaryRefreshingReentry.initial (select (ι := ι) context (active,.ready (ComponentTerminalController.finalState target.focus.rootRecord.1))))
      middle (some .done) final refreshReads refreshCost := refresh
  have actual := MultiSourceFinish.finish (select context) PrimaryRefreshingReentry.initial PrimaryRefreshingReentry.target bodyRun back
  have erasedFinal : (final.mask active).mapRecords Prod.fst = plainFinal :=
    (congrArg (MultiSourceProgram.Configuration.mask active) finalErases).trans plainMiddle
  refine ⟨target,finalForest,active,final,_,_,sameTree,actual,finalRep,finalUnique,?_,?_,correctHeader,finalValid,?_⟩
  · exact finalAssembled.trans (congrArg some erasedFinal.symm)
  · rw [← erasedFinal] at exposed
    exact OriginalAccessController.exposes_unmask final active _ _ (OriginalAccessController.exposes_lift _ _ _ exposed)
  · omega

end TangoSquared.Paper20261030.SecondaryDecomposition.CachedTerminalController
