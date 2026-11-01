import MultiSplay.LayeredBoundedServices
import MultiSplay.RotationSupport

/-! # Bounded simulation of rotations at arbitrary source depths -/

namespace MultiSplay.Layered.Bounded

open Splay.Tree (BST)
open DynamicOptimality (RawTree)
open Splay.Accounting.OfflineConnectedSupport (RootPrefix SupportedPath heavyHeight)

variable {α : Type*}

theorem State.refl_preparation {capacity : Nat} (state : Layered.State capacity α) :
    Preparation capacity state.actual state.actual 0 := by
  have hh := state.component.heavyRep.height_le_capacity state.component.fits
  have rh := state.component.ribRep.height_le state.component.heavyFits
  have he : state.component.heavy.height ≤ heavyHeight capacity := by dsimp [heavyHeight]; omega
  have hm := Nat.mul_le_mul_right (5 * Nat.clog 2 (capacity + 1)) he
  exact .segment state.alphabet (.nil _ (by dsimp [height, Rib.simulationHeight]; omega)
    (BoundedMacros.ribs_mono _ state.component.ribRep.geometry.1 (by omega))) (by omega)

theorem simulate_shallow_source {capacity lower upper : Nat} {before after : BST lower upper}
    {first : RootPrefix before} {last : RootPrefix after} (path : SupportedPath first last)
    (shallow : path.DepthBound 1) (alphabet : Nat → α)
    (state : Layered.State capacity α) (same : state.source = Auxiliary.map alphabet (DynamicOptimality.BST.toRaw before)) :
    ∃ result : Layered.State capacity α, ∃ cost : Nat,
      result.source = Auxiliary.map alphabet (DynamicOptimality.BST.toRaw after) ∧
      Preparation capacity state.actual result.actual cost ∧
      cost + 18 * result.potential ≤ 18 * state.potential + 360004608 * path.length := by
  induction path generalizing state with
  | nil => exact ⟨state, 0, same, State.refl_preparation state, by simp [SupportedPath.length]⟩
  | cons rotation supported tail ih =>
      have raw := Rotation.of_indexed rotation alphabet
      obtain ⟨middle, work, sourceEq, run, bound⟩ := rotate_exists state (same ▸ raw) shallow.1
      obtain ⟨result, cost, resultEq, rest, restBound⟩ := ih shallow.2 middle sourceEq
      refine ⟨result, 18 * work + cost, resultEq, run.trans rest, ?_⟩
      have depthBound := shallow.1
      simp only [SupportedPath.length]
      omega

/-- Deep source rotations are expanded before normalization. The depth charge
pays for this expansion, so the output height remains independent of depth. -/
theorem rotate_trace {capacity depth : Nat} (state : Layered.State capacity α) {target : RawTree α}
    (rotation : Rotation depth state.source target) :
    ∃ result : Layered.State capacity α, ∃ cost : Nat,
      result.source = target ∧ Trace capacity [state.actual] [] [result.actual] cost ∧
      cost + 18 * result.potential ≤ 18 * state.potential + 2880036864 * (depth + 1) := by
  obtain ⟨targetTree, indexed, same⟩ := rotation.lift state.component.source state.alphabet rfl
  obtain ⟨first, last, path, shallow, countBound⟩ := rotation_shallow indexed
  obtain ⟨result, cost, resultEq, run, bound⟩ := simulate_shallow_source path shallow state.alphabet state rfl
  refine ⟨result, cost, resultEq.trans same, CommonForest.Trace.single (.prepare run), ?_⟩
  omega

end MultiSplay.Layered.Bounded
