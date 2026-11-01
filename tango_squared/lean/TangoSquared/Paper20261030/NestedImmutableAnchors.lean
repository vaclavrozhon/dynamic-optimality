import TangoSquared.Paper20261030.MultiSourceImmutableMetadataLabels
import TangoSquared.Paper20261030.RegisterExtensionWriteLabels
import TangoSquared.Paper20261030.MultiSourceNestedImmutable
import TangoSquared.Paper20261030.SourceInorderLabels
import TangoSquared.Paper20261030.MultiSourceRunDeterminism

set_option autoImplicit false

/-! Parked extra fingers retain their physical vertex id throughout a
nested immutable component execution. The actual output is identified
by determinism with the independently label-checked execution. This does
not infer anchor identity merely from validity or a global id inventory. -/

namespace TangoSquared.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer

variable {α ρ τ F : Type*} [DecidableEq F]

theorem Configuration.extend_mapRecords (erase : ρ → τ) (config : Configuration F α ρ)
    (outside : List (Frame α ρ)) :
    (config.extend outside).mapRecords erase = (config.mapRecords erase).extend (outside.map (Frame.mapRecords erase)) := by
  apply congrArg₂ Configuration.mk
  · simp only [Configuration.mapRecords,Configuration.extend_tree,plug_mapRecords]
  · funext finger
    simp only [Configuration.mapRecords,Configuration.extend_finger,← List.map_reverse,List.map_map,
      Function.comp_def,SourcePositions.direction_mapRecords]

end TangoSquared.Paper20261030.MultiSourceProgram

namespace TangoSquared.Paper20261030.MultiSourceNestedImmutable

open ColoredStorage SourcePointer MultiSourceProgram MultiSourceRegisterExtension

variable {α ρ ι F G σ : Type*} [DecidableEq F] [DecidableEq G]

theorem checked (source : Program σ F ρ) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (component : Configuration F α (ι × ρ)) (erases : component.mapRecords Prod.snd = before)
    (outside : List (Frame α (ι × ρ))) (global : Configuration (Sum F G) α (ι × ρ))
    (represented : project global = component.extend outside)
    {target : Configuration (Sum F G) α (ι × ρ)} {actualReads actualCost}
    (actual : Run (program source) (.ready state) global (.ready last) target actualReads actualCost) :
    MultiSourceWriteLabels.Run Prod.fst (program source) (.ready state) global (.ready last) target actualReads actualCost := by
  have extendedErases : (component.extend outside).mapRecords Prod.snd =
      before.extend (outside.map (Frame.mapRecords Prod.snd)) := by
    rw [Configuration.extend_mapRecords,erases]
  obtain ⟨localTarget,localReads,localCost,checked,_,_,_⟩ :=
    MultiSourceImmutable.compile_metadata_run (run.extend (outside.map (Frame.mapRecords Prod.snd)))
      (component.extend outside) extendedErases
  obtain ⟨checkedTarget,checkedRun,_⟩ := compile_write_labels Prod.fst checked global represented
  have same := checkedRun.run.deterministic actual
  rw [← same.2.1,← same.2.2.1,← same.2.2.2]
  exact checkedRun

theorem anchors (source : Program σ F ρ) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (component : Configuration F α (ι × ρ)) (erases : component.mapRecords Prod.snd = before)
    (outside : List (Frame α (ι × ρ))) (global : Configuration (Sum F G) α (ι × ρ))
    (represented : project global = component.extend outside)
    {target : Configuration (Sum F G) α (ι × ρ)} {actualReads actualCost}
    (actual : Run (program source) (.ready state) global (.ready last) target actualReads actualCost) :
    ∀ extra : G, fingerLabel Prod.fst target (.inr extra) = fingerLabel Prod.fst global (.inr extra) := by
  intro extra
  exact (checked source run component erases outside global represented actual).finger_label Prod.fst
    (.inr extra) (keeps_extra _ extra)

theorem inorderLabels (source : Program σ F ρ) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (component : Configuration F α (ι × ρ)) (erases : component.mapRecords Prod.snd = before)
    (outside : List (Frame α (ι × ρ))) (global : Configuration (Sum F G) α (ι × ρ))
    (represented : project global = component.extend outside)
    {target : Configuration (Sum F G) α (ι × ρ)} {actualReads actualCost}
    (actual : Run (program source) (.ready state) global (.ready last) target actualReads actualCost) :
    target.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst :=
  (checked source run component erases outside global represented actual).inorderLabels Prod.fst

end TangoSquared.Paper20261030.MultiSourceNestedImmutable
