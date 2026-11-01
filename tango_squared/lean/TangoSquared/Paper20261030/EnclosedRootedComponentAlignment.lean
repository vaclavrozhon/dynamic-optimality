import TangoSquared.Paper20261030.EnclosedComponentAlignment
import TangoSquared.Paper20261030.EnclosedRootedComponentExecution
import TangoSquared.Paper20261030.RootedComponentWriteLabels
import TangoSquared.Paper20261030.ComponentVirtualRoot

set_option autoImplicit false

/-! Root-to-root secondary compilation preserves the global physical
packet invariants through enclosing-prefix and parent repair. In
particular, packet ids still denote the vertices actually storing them;
all reserved marker ids remain absent. The cost bound is unchanged. -/

namespace TangoSquared.Paper20261030.EnclosedRootedComponentExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open MultiSourceProgram

variable {α β ρ ι η G σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem execute_aligned (markerId : ι) (source : SourceLocalProgram.Program σ ρ) (color : α → Option Bool) (headerKey : α)
    (payload : Option Bool → α → Source β (Packet α ρ ι η))
    {initial last : σ} {before after : Source α ρ} {sourceReads sourceCost}
    (run : SourceLocalProgram.Run source initial ⟨before,[]⟩ last ⟨after,[]⟩ sourceReads sourceCost)
    (decorated : Source α (η × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest)
    (config : Configuration (Option Bool) β (Packet α ρ ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (component : Configuration (Option Bool) β (Cell α ρ ι η))
    (componentErases : component.mapRecords Prod.snd = config)
    (outside : List (Frame β (Cell α ρ ι η)))
    (global : Configuration (Sum (Option Bool) G) β (Cell α ρ ι η))
    (globalRep : MultiSourceRegisterExtension.project global = component.extend outside)
    (valid : WellFormed global) (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨component.tree,outside⟩ global)
    (saved : Packet α ρ ι η) :
    ∃ (target : Source α (η × ρ)), ∃ finalForest finalConfig,
      ∃ (finalComponent : Configuration (Option Bool) β (Cell α ρ ι η)), ∃ actualConfig reads cost,
      Run (EnclosedComponentExecution.program entry saved.length
          (headerPath (representation none wingOrientation headerKey payload forest)).length
          (!outside.isEmpty) (LocalComponentCompiler.program source none wingOrientation)
          (ready initial decorated.rootRecord.1))
        (.first .start) (MultiSourcePacketPrefix.attached saved component.tree outside global)
        (.second (some ⟨component.tree.rootRecord.1,finalComponent.tree.rootRecord.1,.ready (ready last target.rootRecord.1)⟩)
          (some .done)) actualConfig reads cost ∧
      target.mapRecords Prod.snd = after ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved component.tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) actualConfig ∧
      actualConfig.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId actualConfig.tree ∧
      markerId ∉ actualConfig.tree.inventory Prod.fst ∧ WellFormed actualConfig ∧ cost ≤ 948480*sourceCost+13 := by
  obtain ⟨target,finalForest,finalConfig,reads,cost,body,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,_,bound⟩ :=
    RootedComponentExecution.compile_write_labels source color headerKey payload run decorated erases logicalUnique
      forest represented physicalUnique config assembled
  let finalPieces := representation none wingOrientation headerKey payload finalForest
  obtain ⟨header,headerPresent⟩ := virtual_present_root none wingOrientation headerKey payload finalForest
  have canonical : finalConfig = configuration finalPieces ⟨header,[]⟩ :=
    Option.some.inj (finalAssembly.symm.trans (assemble_configuration finalPieces ⟨header,[]⟩ headerPresent))
  have samePath : headerPath finalPieces = headerPath (representation none wingOrientation headerKey payload forest) := by
    exact congrArg₂ (fun (right left : Bool) =>
      (if right then [false] else []) ++ (if left then [true] else []))
      (presence (some false)) (presence (some true))
  obtain ⟨finalComponent,actualConfig,observed,total,actual,componentRep,returned,globalIds,finalPhysical,finalReserved,finalValid,bounded⟩ :=
    EnclosedComponentExecution.execute_aligned markerId _ body component componentErases outside global globalRep valid physical reserved
      entry entryRep saved finalPieces header canonical
      (headerPath (representation none wingOrientation headerKey payload forest)).length
      (congrArg List.length samePath.symm)
  exact ⟨target,finalForest,finalConfig,finalComponent,actualConfig,observed,total,actual,targetErases,ids,
    finalRep,finalUnique,finalAssembly,presence,componentRep,returned,globalIds,finalPhysical,finalReserved,finalValid,by omega⟩

end TangoSquared.Paper20261030.EnclosedRootedComponentExecution
