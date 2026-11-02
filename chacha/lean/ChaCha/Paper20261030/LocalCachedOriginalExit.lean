import ChaCha.Paper20261030.LocalCachedComponentAccess
import ChaCha.Paper20261030.LocalCachedTerminalExposure

/-! Original-key AccessExit with reusable registers and correct final
primary root metadata. A complete secondary update is followed by a
read-only terminal traversal. The saved logical root identifier survives
that traversal and is installed at the physical component root before
returning with the actual exit payload exposed.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.CachedOriginalExitController

open PreferredProjection ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler ComponentAccessController ForestConnector.ThreeColors

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

variable {β ι η : Type*} [DecidableEq ι] [DecidableEq η]

abbrev Record (ι η : Type*) := CachedComponentController.Record ι η
abbrev ControllerState (ι η : Type*) := MultiSourceFinish.State
  (CachedComponentController.ControllerState ι η) (Option (CachedTerminalController.ControllerState ι η))
  (PrimaryRefreshingReentry.Parameters η)

def select : CachedComponentController.ControllerState ι η → PrimaryRefreshingReentry.Parameters η
  | .second parameters _ => parameters
  | _ => none

def terminalInitial (height : Nat) (request : Int) (parameters : PrimaryRefreshingReentry.Parameters η) :
    Option (CachedTerminalController.ControllerState ι η) :=
  parameters.map (CachedTerminalController.initial height request)

def terminalProgram (height : Nat) (request : Int) : PrimaryRefreshingReentry.Parameters η →
    MultiSourceProgram.Program (Option (CachedTerminalController.ControllerState ι η)) (Option Bool) (Record ι η)
  | some context,some phase => (CachedTerminalController.program height request context phase).mapState some
  | _,_ => .halt

def program (origin : Option Bool) (height : Nat) (request : Int) :
    MultiSourceProgram.Program (ControllerState ι η) (Option Bool) (Record ι η) :=
  MultiSourceFinish.program (CachedComponentController.program origin height request) select
    (terminalInitial height request) (terminalProgram height request)

def initial (origin : Option Bool) (height : Nat) (request : Int) : ControllerState ι η :=
  MultiSourceFinish.enter (CachedComponentController.program origin height request) select
    (terminalInitial height request) (CachedComponentController.initial origin height request)

theorem access {a b H : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (origin : Option Bool) (request : Int) (header : PrimaryHeaderController.Header η)
    (validRequest : Dyadic.ValidKey H request) (validBottom : Dyadic.ValidKey H header.bottom)
    (valid : a ≤ Dyadic.lcaDepth H request header.bottom ∧ Dyadic.lcaDepth H request header.bottom ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup) (rootId : header.rootId = decorated.rootRecord.1)
    (forest : TaggedForest (Option Bool) Nat (LogicalRecord η (Option Bool)) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (realColor : color (Dyadic.lcaDepth H request header.bottom) ≠ none)
    (headerKey : Nat) (payload : Option Bool → Nat → Source β (List (Option (Datum ι η (Option Bool)))))
    (headerTree : Source β (List (Option (Datum ι η (Option Bool)))))
    (headerPresent : representation none LocalComponentCompiler.wingOrientation headerKey payload forest none = some ⟨headerTree,[]⟩)
    (leftWing : header.leftWing = (representation none LocalComponentCompiler.wingOrientation headerKey payload forest (some true)).isSome)
    (rightWing : header.rightWing = (representation none LocalComponentCompiler.wingOrientation headerKey payload forest (some false)).isSome)
    (config : MultiSourceProgram.Configuration (Option Bool) β (Record ι η))
    (validConfig : MultiSourceProgram.WellFormed config) (atRoot : config.fingers origin = some [])
    (tree : config.tree.mapRecords Prod.fst =
      (configuration (representation none LocalComponentCompiler.wingOrientation headerKey payload forest) ⟨headerTree,[]⟩).tree)
    (stored : config.tree.rootRecord.2 = some header) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Cursor Nat (η × Cached)),
      ∃ finalForest finalBits finalConfig finalState reads cost,
      Represents followsRight (source reference (Secondary.intervalUpdate (Dyadic.lcaDepth H request header.bottom) preferences)) out ∧
      target.tree.mapRecords Prod.snd = closed out ∧ target.tree.inventory Prod.fst = decorated.inventory Prod.fst ∧
      MultiSourceProgram.Run (program origin H request) (initial origin H request) config finalState finalConfig reads cost ∧
      ProjectionForest.Represents color (cursor Prod.fst color target) (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest)
        (layout (representation none LocalComponentCompiler.wingOrientation headerKey payload forest)) =
        some ((finalConfig.mask finalBits).mapRecords Prod.fst) ∧
      OriginalAccessController.Exposes finalConfig (color (Dyadic.lcaDepth H request header.bottom))
        (payload (color (Dyadic.lcaDepth H request header.bottom)) (Dyadic.lcaDepth H request header.bottom)) ∧
      finalConfig.tree.rootRecord.2 = some {header with rootId := target.tree.rootRecord.1} ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 2*((118560*(Fintype.card (Option Bool)+1))*
        (((Secondary.decodeDepth reference preferences).accessFlips (Dyadic.lcaDepth H request header.bottom)+1)*AccessController.bound reference)) +
        2*((59280*(Fintype.card (Option Bool)+1))*(6*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+1))+27 := by
  let depth := Dyadic.lcaDepth H request header.bottom
  let physical := representation none LocalComponentCompiler.wingOrientation headerKey payload forest
  obtain ⟨out,updated,middleForest,active,middle,firstReads,firstCost,outRep,updatedErases,inventory,firstRun,
      middleRep,middleUnique,middleAssembled,middleCovered,presence,middleHeader,middleValid,firstBound⟩ :=
    CachedComponentController.access reference preferences origin request header validRequest validBottom valid component represented
      color decorated erases logicalUnique rootId forest forestRep physicalUnique headerKey payload headerTree headerPresent leftWing rightWing
      config validConfig atRoot tree stored
  let context : PrimaryRefreshingReentry.Context η := ⟨header,updated.rootRecord.1,active⟩
  let middlePhysical := representation none LocalComponentCompiler.wingOrientation headerKey payload middleForest
  have endpoint : (Secondary.decodeDepth reference (Secondary.intervalUpdate depth preferences)).terminal = depth := by
    rw [Secondary.decodeDepth_access]
    exact PrefRouter.terminal_access _ _ ((Secondary.decodeDepth_mem reference preferences depth).mpr valid)
  have updatedUnique : (updated.inventory Prod.fst).Nodup := by rw [inventory]; exact logicalUnique
  have changedLayout : layout middlePhysical = layout physical := layout_congr physical middlePhysical presence
  have readyAssembled : ForestConnector.assemble middlePhysical (layout middlePhysical) = some ((middle.mask active).mapRecords Prod.fst) := by
    rw [changedLayout]; exact middleAssembled
  obtain ⟨target,finalForest,finalBits,finalConfig,lastReads,lastCost,sameTree,lastRun,finalRep,finalUnique,
      finalAssembled,exposed,finalHeader,finalValid,lastBound⟩ :=
    CachedTerminalController.expose reference (Secondary.intervalUpdate depth preferences) request context validRequest validBottom endpoint
      out outRep color updated updatedErases updatedUnique rfl middleForest middleRep middleUnique realColor headerKey payload
      (leftWing.trans (presence (some true)).symm) (rightWing.trans (presence (some false)).symm) middle middleValid readyAssembled
  have terminalSteps := lastRun.map_prefix (target := terminalProgram H request (some context)) some (fun _ _ => rfl)
  have terminalRun := terminalSteps.run (by
    simp only [terminalProgram,lastRun.halted,MultiSourceProgram.Instruction.mapState])
  have back : MultiSourceProgram.Run (terminalProgram H request (select (.second (some context) (some .done) : CachedComponentController.ControllerState ι η)))
      (terminalInitial H request (select (.second (some context) (some .done) : CachedComponentController.ControllerState ι η)))
      middle _ finalConfig lastReads lastCost := terminalRun
  have actual := MultiSourceFinish.finish select (terminalInitial H request) (terminalProgram H request) firstRun back
  refine ⟨out,target,finalForest,finalBits,finalConfig,_,_,_,outRep,?_,?_,actual,finalRep,finalUnique,?_,exposed,?_,finalValid,?_⟩
  · rw [sameTree]; exact updatedErases
  · rw [sameTree]; exact inventory
  · change ForestConnector.assemble _ (layout middlePhysical) = _ at finalAssembled
    rw [changedLayout] at finalAssembled
    exact finalAssembled
  · rw [sameTree]; exact finalHeader
  · omega

end ChaCha.Paper20261030.SecondaryDecomposition.CachedOriginalExitController
