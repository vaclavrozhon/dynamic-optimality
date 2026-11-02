import ChaCha.Paper20261030.ComponentRootRegister
import ChaCha.Paper20261030.PrimaryRefreshingReentry
import ChaCha.Paper20261030.ThreeColorLayoutStability
import ChaCha.Paper20261030.ComponentRootPositions
import ChaCha.Paper20261030.ComponentOriginalKeys

/-! Complete original-key secondary access with reusable physical
registers and refreshed primary root metadata. The request depth is
computed from the header actually read at entry. The complete secondary
update ends at its source root; its compiler register supplies the new
identifier for the final charged cache repair. Terminal-payload exposure
and the enclosing primary head-switch loop remain separate.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.CachedComponentController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler ComponentAccessController ForestConnector.ThreeColors

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

variable {β ι η : Type*} [DecidableEq ι] [DecidableEq η]

abbrev Record (ι η : Type*) := PrimaryHeaderController.Record (List (Option (Datum ι η (Option Bool)))) η
abbrev ControllerState (ι η : Type*) := PrimaryRefreshingReentry.State
  (ComponentAccessController.ControllerState ι η (Option Bool)) (Option (Datum ι η (Option Bool))) η

def program (origin : Option Bool) (height : Nat) (request : Int) :
    MultiSourceProgram.Program (ControllerState ι η) (Option Bool) (Record ι η) :=
  PrimaryRefreshingReentry.program origin height request ComponentAccessController.initial
    (fun depth => ComponentAccessController.program depth none LocalComponentCompiler.wingOrientation) rootRegister

def initial (origin : Option Bool) (height : Nat) (request : Int) : ControllerState ι η :=
  MultiSourceFinish.enter
    (PrimaryReentryController.program origin height request ComponentAccessController.initial
      (fun depth => ComponentAccessController.program depth none LocalComponentCompiler.wingOrientation))
    (PrimaryRefreshingReentry.select rootRegister) PrimaryRefreshingReentry.initial
    (PrimaryReentryController.reset MultiSourceRecenter.three)

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
    (physicalUnique : Unique forest)
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
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)),
      ∃ finalForest finalBits finalConfig reads cost,
      Represents followsRight (source reference (Secondary.intervalUpdate (Dyadic.lcaDepth H request header.bottom) preferences)) out ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      MultiSourceProgram.Run (program origin H request) (initial origin H request) config
        (.second (some ⟨header,target.rootRecord.1,finalBits⟩) (some .done)) finalConfig reads cost ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest)
        (layout (representation none LocalComponentCompiler.wingOrientation headerKey payload forest)) =
        some ((finalConfig.mask finalBits).mapRecords Prod.fst) ∧
      ForestConnector.Covers (layout (representation none LocalComponentCompiler.wingOrientation headerKey payload forest))
        (representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest) ∧
      (∀ q, (representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest q).isSome =
        (representation none LocalComponentCompiler.wingOrientation headerKey payload forest q).isSome) ∧
      finalConfig.tree.rootRecord.2 = some {header with rootId := target.rootRecord.1} ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 2*((118560*(Fintype.card (Option Bool)+1))*
        (((Secondary.decodeDepth reference preferences).accessFlips (Dyadic.lcaDepth H request header.bottom)+1)*
          AccessController.bound reference))+21 := by
  let depth := Dyadic.lcaDepth H request header.bottom
  let physical := representation none LocalComponentCompiler.wingOrientation headerKey payload forest
  let plainConfig := configuration physical ⟨headerTree,[]⟩
  have assembled := assemble_configuration physical ⟨headerTree,[]⟩ headerPresent
  obtain ⟨out,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    AccessController.access reference preferences depth valid component represented []
  have cursorErases : (Cursor.mapRecords Prod.snd ⟨decorated,[]⟩ : Cursor Nat Cached) = ⟨closed component,[]⟩ := by
    simp only [Cursor.mapRecords,erases,List.map_nil]
  obtain ⟨targetCursor,finalForest,plainFinal,plainReads,plainCost,plainRun,targetErases,inventory,
      finalRep,finalUnique,finalAssembled,finalCovered,plainValid,compiledBound⟩ :=
    LocalComponentCompiler.compile_run (AccessController.program depth) color none LocalComponentCompiler.wingOrientation
      headerKey payload sourceRun ⟨decorated,[]⟩ cursorErases logicalUnique forest forestRep physicalUnique
      (layout physical) (distinct physical) (covers physical) plainConfig assembled
  have root : targetCursor.ancestors = [] := by
    have equal := congrArg Cursor.ancestors targetErases
    simpa only [Cursor.mapRecords,List.map_eq_nil_iff] using equal
  have finalRootRep : ProjectionForest.Represents color
      ⟨annotate Prod.fst color none targetCursor.focus,[]⟩ (erase finalForest) := by
    simpa only [cursor,root,frames,parentId] using finalRep
  let finalPhysical := representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest
  obtain ⟨headerCursor,finalHeaderPresent⟩ := LocalComponentCompiler.virtual_present none LocalComponentCompiler.wingOrientation headerKey payload finalForest
  have headerRoot : headerCursor.ancestors = [] := LocalComponentCompiler.representation_root color targetCursor.focus
    finalForest finalRootRep none LocalComponentCompiler.wingOrientation headerKey payload none headerCursor finalHeaderPresent
  have finalHeader : finalPhysical none = some ⟨headerCursor.focus,[]⟩ := by
    change representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest none = _
    rw [finalHeaderPresent,← headerRoot]
  obtain ⟨presence,canonical⟩ := canonical_final physical finalPhysical plainConfig plainFinal assembled finalAssembled finalCovered headerCursor.focus finalHeader
  have rooted : ∀ q current, physical q = some current → current.ancestors = [] :=
    LocalComponentCompiler.representation_root color decorated forest forestRep none LocalComponentCompiler.wingOrientation headerKey payload
  change MultiSourceProgram.Run (ComponentAccessController.program depth none LocalComponentCompiler.wingOrientation)
    (ComponentAccessController.initial decorated.rootRecord.1) plainConfig
    (ComponentAccessController.finalState targetCursor.focus.rootRecord.1) plainFinal plainReads plainCost at plainRun
  rw [← rootId] at plainRun
  obtain ⟨active,middle,middleReads,middleCost,front,middleErases,validMiddle,metadata,entryBound⟩ :=
    PrimaryReentryController.dispatch origin H request ComponentAccessController.initial
      (fun depth => ComponentAccessController.program depth none LocalComponentCompiler.wingOrientation)
      physical headerTree rooted header leftWing rightWing config validConfig atRoot tree stored validRequest validBottom plainRun
  obtain ⟨final,reads,cost,actual,finalErases,correctHeader,finalValid,refreshBound⟩ :=
    PrimaryRefreshingReentry.append_refresh origin H request ComponentAccessController.initial
      (fun depth => ComponentAccessController.program depth none LocalComponentCompiler.wingOrientation) rootRegister
      header targetCursor.focus.rootRecord.1 (ComponentAccessController.finalState targetCursor.focus.rootRecord.1) rfl
      active config middle middleReads middleCost front validMiddle finalPhysical headerCursor.focus
      (leftWing.trans (presence (some true)).symm) (rightWing.trans (presence (some false)).symm)
      (middleErases.trans canonical)
  have maskedErases : (final.mask active).mapRecords Prod.fst = (middle.mask active).mapRecords Prod.fst :=
    congrArg (MultiSourceProgram.Configuration.mask active) finalErases
  refine ⟨out,targetCursor.focus,finalForest,active,final,reads,cost,outRep,congrArg Cursor.focus targetErases,?_,actual,
    finalRootRep,finalUnique,?_,finalCovered,presence,correctHeader,finalValid,?_⟩
  · simpa only [Cursor.tree,plug,root] using inventory
  · exact finalAssembled.trans (congrArg some (maskedErases.trans middleErases).symm)
  · have fullBound := compiledBound.trans (Nat.mul_le_mul_left _ sourceBound)
    dsimp only [depth] at fullBound
    omega

end ChaCha.Paper20261030.SecondaryDecomposition.CachedComponentController
