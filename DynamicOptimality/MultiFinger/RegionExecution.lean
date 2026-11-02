import DynamicOptimality.MultiFinger.RegionReplacement
import DynamicOptimality.MultiFinger.RegionStep
import DynamicOptimality.GeometricOnlineSimulation.Graft

/-!
# Realizing symbolic region steps in arbitrary physical top trees

Equal marker and hole words determine the entire physical inorder word,
even when the top shapes differ. This lets a symbolic local region step
act on whichever top tree the preceding splay operations actually left.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation
open ChaCha.Paper20261030.SplayAuxiliary (potential)

variable {α : Type*}

theorem DataEquivalent.skeleton_size {before after : MarkedTree α}
    (same : DataEquivalent before after) : before.skeleton.size = after.skeleton.size := by
  simpa only [Tree.length_inorder] using congrArg List.length same.1

theorem DataEquivalent.erase_word {before after : MarkedTree α}
    (same : DataEquivalent before after) : before.erase.inorder = after.erase.inorder := by
  have arrays : before.gapArray = after.gapArray := by
    funext index
    simp only [MarkedTree.gapArray, same.2]
  obtain ⟨count, _, run⟩ := Tree.graft_simulation_linear before.skeleton after.skeleton
    same.1 before.gapArray 0
  rw [before.graft_gapArray, arrays, after.graft_gapArray] at run
  exact run.inorder_eq

namespace RegionContext

def prepend (cells : List (α × RawTree α)) (context : MarkedTree.Context α) :
    MarkedTree.Context α :=
  match cells with
  | [] => context
  | (key, gap) :: rest => .right (.hole gap) key (prepend rest context)

def append (context : MarkedTree.Context α) (cells : List (α × RawTree α)) :
    MarkedTree.Context α :=
  match cells with
  | [] => context
  | (key, gap) :: rest => append (.left key (.hole gap) context) rest

theorem prepend_words (cells : List (α × RawTree α)) (context : MarkedTree.Context α) :
    (prepend cells context).keysBefore = cells.map Prod.fst ++ context.keysBefore ∧
    (prepend cells context).keysAfter = context.keysAfter ∧
    (prepend cells context).holesBefore = cells.map Prod.snd ++ context.holesBefore ∧
    (prepend cells context).holesAfter = context.holesAfter := by
  induction cells with
  | nil => simp [prepend]
  | cons cell rest ih =>
      rcases cell with ⟨key, gap⟩
      rcases ih with ⟨first, last, front, back⟩
      simp [prepend, MarkedTree.Context.keysBefore, MarkedTree.Context.keysAfter,
        MarkedTree.Context.holesBefore, MarkedTree.Context.holesAfter,
        MarkedTree.skeleton, MarkedTree.holes, Tree.inorder, first, last, front, back]

theorem append_words (cells : List (α × RawTree α)) (context : MarkedTree.Context α) :
    (append context cells).keysBefore = context.keysBefore ∧
    (append context cells).keysAfter = context.keysAfter ++ cells.map Prod.fst ∧
    (append context cells).holesBefore = context.holesBefore ∧
    (append context cells).holesAfter = context.holesAfter ++ cells.map Prod.snd := by
  induction cells generalizing context with
  | nil => simp [append]
  | cons cell rest ih =>
      rcases cell with ⟨key, gap⟩
      rcases ih (.left key (.hole gap) context) with ⟨first, last, front, back⟩
      refine ⟨first, ?_, front, ?_⟩
      · simpa only [append, MarkedTree.Context.keysAfter, MarkedTree.skeleton,
          Tree.inorder, List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using last
      · simpa only [append, MarkedTree.Context.holesAfter, MarkedTree.holes,
          List.map_cons, List.append_assoc, List.singleton_append] using back

end RegionContext

/-- This context is only a word witness. Unlike `RegionFrame.expose`, it
does not claim that the current physical top shape already has that gap. -/
theorem RegionFrame.exists_context (frame : RegionFrame α) :
    ∃ context : MarkedTree.Context α, frame.Matches context := by
  let front := frame.beforeKeys.zip frame.beforeHoles
  let back := frame.afterKeys.zip frame.afterHoles
  have frontKeys : front.map Prod.fst = frame.beforeKeys :=
    List.map_fst_zip (Nat.le_of_eq frame.beforeCount.symm)
  have frontHoles : front.map Prod.snd = frame.beforeHoles :=
    List.map_snd_zip (Nat.le_of_eq frame.beforeCount)
  have backKeys : back.map Prod.fst = frame.afterKeys :=
    List.map_fst_zip (Nat.le_of_eq frame.afterCount.symm)
  have backHoles : back.map Prod.snd = frame.afterHoles :=
    List.map_snd_zip (Nat.le_of_eq frame.afterCount)
  let last := RegionContext.append .top back
  rcases RegionContext.append_words back (.top : MarkedTree.Context α) with ⟨a, b, c, d⟩
  rcases RegionContext.prepend_words front last with ⟨e, f, g, h⟩
  refine ⟨RegionContext.prepend front last, ?_⟩
  change _ ∧ _ ∧ _ ∧ _
  simp only [e, f, g, h, last, a, b, c, d, MarkedTree.Context.keysBefore,
    MarkedTree.Context.keysAfter, MarkedTree.Context.holesBefore, MarkedTree.Context.holesAfter,
    List.nil_append, List.append_nil, frontKeys, frontHoles, backKeys, backHoles, and_self]

/-- A symbolic step preserves every original physical key, independently
of any order, uniqueness, or choice of top-tree shape. -/
theorem RegionStep.word {before after : MarkedTree α} {count : Nat}
    (step : RegionStep before after count) : before.erase.inorder = after.erase.inorder := by
  obtain ⟨frame, oldBlock, newBlock, oldInside, newInside, _, _, raw⟩ := step
  obtain ⟨context, matching⟩ := frame.exists_context
  have oldSame : DataEquivalent before (context.plug oldBlock) := by
    have target := matching.contains oldBlock
    exact ⟨oldInside.1.trans target.1.symm, oldInside.2.trans target.2.symm⟩
  have newSame : DataEquivalent after (context.plug newBlock) := by
    have target := matching.contains newBlock
    exact ⟨newInside.1.trans target.1.symm, newInside.2.trans target.2.symm⟩
  have run := Top.rotations_context context raw
  have middle : (context.plug oldBlock).erase.inorder = (context.plug newBlock).erase.inorder := by
    have conserve : ∀ {first last : RawTree α} {work : Nat},
        Rotations first last work → first.inorder = last.inorder := by
      intro first last work execution
      induction execution with
      | refl => rfl
      | step first rest ih => exact (GeometricOnlineSimulation.rotation_inorder first).trans ih
    exact conserve run
  exact oldSame.erase_word.trans (middle.trans newSame.erase_word.symm)

/-- Execute the canonical local edit starting from any data-equivalent
actual top tree. The output again represents precisely the new canonical
marker and gap words, and its actual rotations obey the amortized bound. -/
theorem RegionStep.realize {before after actual : MarkedTree Nat} {rawCount capacity : Nat}
    (step : RegionStep before after rawCount) (same : DataEquivalent before actual)
    (ordered : actual.erase.Ordered) (fits : actual.skeleton.size ≤ capacity) :
    ∃ (result : MarkedTree Nat) (count : Nat),
      DataEquivalent after result ∧ Rotations actual.erase result.erase count ∧
      count + 2 * potential result.skeleton ≤ 2 * potential actual.skeleton + rawCount +
        32 * (1 + Nat.log 2 (capacity + 4)) := by
  have physicalWord := step.word
  have afterOrdered : after.erase.Ordered := by
    change after.erase.inorder.Pairwise (· < ·)
    rw [← physicalWord, same.erase_word]
    exact ordered
  have unique := Top.skeleton_nodup (afterOrdered.imp (fun less => ne_of_lt less))
  obtain ⟨frame, oldBlock, newBlock, oldInside, newInside, oldSmall, newSmall, raw⟩ := step
  have actualInside : frame.Contains actual oldBlock :=
    ⟨same.1.symm.trans oldInside.1, same.2.symm.trans oldInside.2⟩
  obtain ⟨result, count, contained, run, bound⟩ := regionReplacementBound frame actual oldBlock newBlock
    rawCount capacity actualInside ordered (by rw [← newInside.1]; exact unique)
    fits oldSmall newSmall raw
  exact ⟨result, count, ⟨newInside.1.trans contained.1.symm, newInside.2.trans contained.2.symm⟩,
    run, bound⟩

end DynamicOptimality.MultiFinger
