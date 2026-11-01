import TangoSquared.Paper20261030.ReenteredComponentExecution
import TangoSquared.Paper20261030.RootedComponentWriteLabels
import TangoSquared.Paper20261030.ComponentRootPositions
import TangoSquared.Paper20261030.EnclosedRootedComponentExecution

set_option autoImplicit false

/-! Source-root-to-root compilation from one reached physical root.
The eight-operation setup is part of the controller. Enclosing repair,
whole-tree packet alignment, immutable ids, and final observations remain
available; arbitrary initial placements of working fingers are allowed. -/

namespace TangoSquared.Paper20261030.ReenteredRootedComponentExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open MultiSourceProgram
open EnclosedRootedComponentExecution (Packet Cell)

variable {α β ρ ι η G σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem execute (markerId : ι) (source : SourceLocalProgram.Program σ ρ) (color : α → Option Bool) (headerKey : α)
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
    (tree : Source β (Cell α ρ ι η)) (treeErases : tree.mapRecords Prod.snd = config.tree)
    (outside : List (Frame β (Cell α ρ ι η)))
    (global : Configuration (Sum (Option Bool) G) β (Cell α ρ ι η))
    (valid : WellFormed global) (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨tree,outside⟩ global)
    (saved : Packet α ρ ι η) :
    ∃ (target : Source α (η × ρ)), ∃ finalForest finalConfig,
      ∃ (finalComponent : Configuration (Option Bool) β (Cell α ρ ι η)), ∃ entryBits finalBits actualConfig reads cost,
      Run (ReenteredComponentExecution.program entry
          (representation none wingOrientation headerKey payload forest (some true)).isSome
          (representation none wingOrientation headerKey payload forest (some false)).isSome saved.length
          (headerPath (representation none wingOrientation headerKey payload forest)).length
          (!outside.isEmpty) (LocalComponentCompiler.program source none wingOrientation)
          (ready initial decorated.rootRecord.1))
        (.first .start) (MultiSourcePacketPrefix.attached saved tree outside global)
        (.second (some ⟨tree.rootRecord.1,finalComponent.tree.rootRecord.1,.second entryBits (finalBits,.ready (ready last target.rootRecord.1))⟩)
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
        (EnclosingPacketOperation.output saved tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) actualConfig ∧
      actualConfig.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId actualConfig.tree ∧
      markerId ∉ actualConfig.tree.inventory Prod.fst ∧ WellFormed actualConfig ∧
      actualConfig.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, fingerLabel Prod.fst actualConfig (.inr extra) = fingerLabel Prod.fst global (.inr extra)) ∧
      cost ≤ 948480*sourceCost+21 := by
  obtain ⟨target,finalForest,finalConfig,reads,cost,body,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,_,bound⟩ :=
    RootedComponentExecution.compile_write_labels source color headerKey payload run decorated erases logicalUnique
      forest represented physicalUnique config assembled
  let firstPieces := representation none wingOrientation headerKey payload forest
  let finalPieces := representation none wingOrientation headerKey payload finalForest
  obtain ⟨firstHeader,firstPresent⟩ := virtual_present_root none wingOrientation headerKey payload forest
  obtain ⟨finalHeader,finalPresent⟩ := virtual_present_root none wingOrientation headerKey payload finalForest
  have firstCanonical : config = configuration firstPieces ⟨firstHeader,[]⟩ :=
    Option.some.inj (assembled.symm.trans (assemble_configuration firstPieces ⟨firstHeader,[]⟩ firstPresent))
  have finalCanonical : finalConfig = configuration finalPieces ⟨finalHeader,[]⟩ :=
    Option.some.inj (finalAssembly.symm.trans (assemble_configuration finalPieces ⟨finalHeader,[]⟩ finalPresent))
  rw [firstCanonical] at body treeErases
  obtain ⟨finalComponent,entryBits,finalBits,actualConfig,observed,total,actual,componentRep,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,bounded⟩ :=
    ReenteredComponentExecution.execute markerId entry firstPieces finalPieces firstHeader finalHeader
      (representation_root color decorated forest represented none wingOrientation headerKey payload)
      _ body tree treeErases outside global entryRep valid physical reserved saved finalCanonical presence
  exact ⟨target,finalForest,finalConfig,finalComponent,entryBits,finalBits,actualConfig,observed,total,actual,targetErases,ids,
    finalRep,finalUnique,finalAssembly,presence,componentRep,returned,globalIds,finalPhysical,finalReserved,finalValid,order,anchors,by omega⟩

end TangoSquared.Paper20261030.ReenteredRootedComponentExecution
