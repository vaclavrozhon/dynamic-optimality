import TangoSquared.Paper20261030.MultiSourceDownwardMap
import TangoSquared.Paper20261030.DownwardRegisterInvariants
import TangoSquared.Paper20261030.MultiSourceNestedExecution
import TangoSquared.Paper20261030.MultiSourceRecenter
import TangoSquared.Paper20261030.MultiSourceFinish
import TangoSquared.Paper20261030.ThreeColorEntry

set_option autoImplicit false

/-! Positioning all three component registers from one reached root.
The controller copies the root pointer three times and follows at most
five downward edges. Absent wings are hidden by presence bits. Immutable
records, the outer context, and the physical tree are unchanged. -/

namespace TangoSquared.Paper20261030.NestedComponentEntry

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram
open ForestConnector.ThreeColors MultiSourceRegisterExtension

variable {α ρ τ G : Type*} [DecidableEq G]

def enabled (left right : Bool) : Option Bool → Bool
  | none => true
  | some true => left
  | some false => right

def bits (left right : Bool) : Sum (Option Bool) G → Bool
  | .inl q => enabled left right q
  | .inr _ => true

def destinations : List (Sum (Option Bool) G) := MultiSourceRecenter.three.map Sum.inl

def program (origin : Sum (Option Bool) G) (left right : Bool) :=
  MultiSourceFinish.program (MultiSourceRecenter.program (ρ := ρ) origin) (fun _ => ())
    (fun _ => (bits left right,entrySchedule left right))
    (fun _ => MultiSourceMask.program (MultiSourceRegisterExtension.program MultiSourceDownward.program))

def rooted (tree : Source α ρ) (left right : Bool) : Configuration (Option Bool) α ρ :=
  ⟨tree,fun q => if enabled left right q then some [] else none⟩

theorem masked_wellFormed (mask : (Sum (Option Bool) G) → Bool)
    (config : Configuration (Sum (Option Bool) G) α ρ) (valid : WellFormed config) : WellFormed (config.mask mask) := by
  intro finger position present
  exact valid finger position (mask_present mask config finger position present).2

theorem recentered (origin : Sum (Option Bool) G) (left right : Bool) (tree : Source α ρ)
    (outside : List (Frame α ρ)) (config : Configuration (Sum (Option Bool) G) α ρ)
    (atRoot : MultiSourceSingleCursor.Represents origin ⟨tree,outside⟩ config) :
    project ((MultiSourceRecenter.execute origin config destinations).mask (bits left right)) =
      (rooted tree left right).extend outside := by
  apply congrArg₂ Configuration.mk
  · exact (MultiSourceRecenter.execute_tree origin config destinations).trans
      (atRoot.1.trans ((rooted tree left right).extend_tree outside).symm)
  · funext q
    have member : (Sum.inl q : Sum (Option Bool) G) ∈ destinations :=
      List.mem_map.mpr ⟨q,MultiSourceRecenter.three_covers q,rfl⟩
    change (if bits left right (.inl q) then
      (MultiSourceRecenter.execute origin config destinations).fingers (.inl q) else none) = _
    rw [MultiSourceRecenter.execute_fingers,if_pos member,Configuration.extend_finger]
    simp only [bits,rooted,atRoot.2,address]
    cases enabled left right q <;> simp

theorem execute (erase : ρ → List τ) (origin : Sum (Option Bool) G)
    (forest : ProjectionForest.State (Option Bool) α τ) (header : Source α (List τ))
    (atRoots : ∀ q current, forest q = some current → current.ancestors = [])
    (tree : Source α ρ) (erases : tree.mapRecords erase = (configuration forest ⟨header,[]⟩).tree)
    (outside : List (Frame α ρ)) (config : Configuration (Sum (Option Bool) G) α ρ)
    (atRoot : MultiSourceSingleCursor.Represents origin ⟨tree,outside⟩ config)
    (valid : WellFormed config) :
    ∃ (component : Configuration (Option Bool) α ρ), ∃ finalBits target reads cost,
      Run (program origin (forest (some true)).isSome (forest (some false)).isSome)
        (.first destinations) config (.second () (finalBits,[])) target reads cost ∧
      component.mapRecords erase = configuration forest ⟨header,[]⟩ ∧ component.tree = tree ∧
      project (target.mask finalBits) = component.extend outside ∧
      target.tree = config.tree ∧ WellFormed target ∧
      finalBits = bits (forest (some true)).isSome (forest (some false)).isSome ∧
      (∀ extra : G, target.fingers (.inr extra) = config.fingers (.inr extra)) ∧ cost ≤ 8 := by
  let left := (forest (some true)).isSome
  let right := (forest (some false)).isSome
  let entryConfig := rooted tree left right
  have localErases : entryConfig.mapRecords erase = entryConfiguration forest header := by
    apply congrArg₂ Configuration.mk erases
    funext q
    cases q with
    | none => simp only [entryConfig,rooted,enabled,Configuration.mapRecords,entryConfiguration,if_true]
    | some side => cases side <;> simp [entryConfig,rooted,enabled,left,right,entryConfiguration,Configuration.mapRecords]
  obtain ⟨component,entryRun,componentErases,componentTree⟩ :=
    MultiSourceDownward.lift_run erase (entrySchedule left right) entryConfig (configuration forest ⟨header,[]⟩)
      (by rw [localErases]; exact entry_execute forest header atRoots)
  let centered := MultiSourceRecenter.execute origin config (destinations (G := G))
  have resetRun := MultiSourceRecenter.run origin config (destinations (G := G))
  have centeredValid := resetRun.wellFormed valid
  have centeredRep := recentered origin left right tree outside config atRoot
  obtain ⟨logicalTarget,logicalRun,logicalRep,logicalTree,_,_⟩ :=
    MultiSourceNestedExecution.execute MultiSourceDownward.program entryRun outside
      (centered.mask (bits left right)) centeredRep (masked_wellFormed _ centered centeredValid)
  obtain ⟨finalBits,target,reads,actual,maskEq,finalValid⟩ :=
    MultiSourceMask.compile_run logicalRun (bits left right) centered centeredValid rfl
  have whole := MultiSourceFinish.finish (fun _ => ())
    (fun _ => (bits left right,entrySchedule left right))
    (fun _ => MultiSourceMask.program (MultiSourceRegisterExtension.program MultiSourceDownward.program))
    resetRun actual
  have targetTree : target.tree = config.tree := by
    have sameTree := congrArg (fun c : Configuration (Sum (Option Bool) G) α ρ => c.tree) maskEq
    change target.tree = logicalTarget.tree at sameTree
    rw [sameTree,logicalTree,componentTree]
    exact atRoot.1.symm
  refine ⟨component,finalBits,target,_,_,whole,componentErases,componentTree,?_,targetTree,finalValid,?_,?_,?_⟩
  · rw [maskEq]
    exact logicalRep
  · funext finger
    exact MultiSourceMask.Run.bit _ finger (MultiSourceDownward.extended_keeps_copy finger) actual
  · intro extra
    have stationary := actual.stationary_finger (.inr extra) (MultiSourceDownward.masked_stationary extra)
    exact stationary.trans (by simp [centered,MultiSourceRecenter.execute_fingers,destinations,MultiSourceRecenter.three])
  · have bound := entrySchedule_bound left right
    simpa only [destinations,MultiSourceRecenter.three,List.length_map,List.length_cons,List.length_nil] using
      (show 3+(entrySchedule left right).length ≤ 8 by omega)

end TangoSquared.Paper20261030.NestedComponentEntry
