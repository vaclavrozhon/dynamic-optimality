import MultiSplay.SharedSplayComponents
import MultiSplay.CommonBends
import Splay.Accounting.ArticleMacroBirthBounds
import Splay.Accounting.WholeSplayTemporaryGeometry
import Splay.Accounting.ComparisonRotationJunctionBound

/-! # Geometric and cost bounds for the actual component macros -/

namespace MultiSplay.MacroGeometry

open Splay.Accounting
open Splay.Accounting.LocalBendGeometry
open Splay.Rank (Snapshot)
open Splay.Tree.BST
open Splay.Assumptions.NormalForm

variable {n : Nat} {params : Splay.Interface.Parameters} {before after : ArticleCheckpoint n}

def Normal (slack depth : Nat) : {before after : ArticleCheckpoint n} → ArticleMacro params before after → Prop
  | _, _, .rotation (depth := actualDepth) _ _ _ => actualDepth ≤ depth
  | before, _, .request _ _ _ _ _ => HasRelevantNeighborRankBound (Snapshot.ofTree before.comparison) slack

noncomputable def potential (checkpoint : ArticleCheckpoint n) : Nat :=
  (bends (Snapshot.ofTree checkpoint.comparison) checkpoint.splay).card

/-- One unit for the request plus its actual number of ordinary rotations. -/
def splayCost : ArticleMacro params before after → Nat
  | .rotation _ _ _ => 0
  | .request (key := key) _ _ _ _ _ => before.splay.depth key.val + 1

theorem births (step : ArticleMacro params before after) {slack depth : Nat} (normal : Normal slack depth step) :
    step.birthBudget ≤ articleRequestBirthBudget slack * step.requests.length +
      articleFullComparisonBirthBudget depth * step.rotationCount := by
  cases step with
  | rotation represented rotation execution =>
      simpa [ArticleMacro.birthBudget, ArticleMacro.requests, ArticleMacro.rotationCount] using articleFullComparisonBirthBudget_mono normal
  | request represented root execution transcript request =>
      simpa [ArticleMacro.birthBudget, ArticleMacro.requests, ArticleMacro.rotationCount] using request.birthBudget_le root normal

theorem bend_charge (step : ArticleMacro params before after) {slack depth : Nat} (normal : Normal slack depth step) :
    potential after + step.kinds.count .zigZag ≤ potential before + step.kinds.count .zigZig +
      (2 + 6 * (slack+1)) * step.requests.length + 3 * step.rotationCount := by
  cases step with
  | @rotation afterTree actualDepth represented rotation execution =>
      have created := Splay.Accounting.ComparisonRotationJunctionBound.RotationAt.created_le_three rotation (splayTree := before.splay)
      have balance := BendAction.card_balance_between .comparisonRotation 0 0
        (bends (Snapshot.ofTree before.comparison) before.splay)
        (bends (Snapshot.ofTree afterTree) before.splay)
      simp only [ArticleMacro.kinds, List.count_nil, ArticleMacro.requests, List.length_nil,
        ArticleMacro.rotationCount, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
      dsimp only [potential]
      dsimp only [BendAction.between] at balance
      omega
  | @request afterTree key represented root execution transcript request =>
      let constants : BendConstants := ⟨1, 2+6*(slack+1), 3⟩
      let certificate := WholeSplayTemporaryGeometry.completeSplayCertificateOfBounds
        (constants := constants) root
        (WholeSplayTemporaryGeometry.CanonicalSpinePersistence.canonicalEndpointBounds before.comparison key execution root)
        normal (Nat.le_refl _)
      have balance := certificate.bendHistory.telescope
      have sound := certificate.bendAction_locallySound
      rw [BendAction.LocallySound, certificate.bendAction_kind_eq] at sound
      have counts := certificate.transcript.transcript.counts_unique transcript.transcript
      have zz := transcript.transcript.count_zigZig
      have zg := transcript.transcript.count_zigZag
      have actZZ := certificate.bendAction_zigZig_eq
      have actZG := certificate.bendAction_zigZag_eq
      simp only [totalBendsCreated, totalBendsRemoved, Nat.add_zero] at balance
      simp only [potential, ArticleMacro.kinds, ArticleMacro.requests, List.length_cons, List.length_nil,
        ArticleMacro.rotationCount, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
      change certificate.bendAction.zigZag ≤ certificate.bendAction.removed ∧
        certificate.bendAction.created ≤ certificate.bendAction.zigZig + (2+6*(slack+1)) at sound
      omega

theorem splayCost_le (step : ArticleMacro params before after) :
    splayCost step ≤ 2 * step.kinds.count .zigZig + 2 * step.kinds.count .zigZag + 2 * step.requests.length := by
  cases step with
  | rotation represented rotation execution => simp [splayCost, ArticleMacro.kinds, ArticleMacro.requests]
  | request represented root execution transcript request =>
      have depth := transcript.transcript.toExecutionCounts.depth_eq_and_zig_le_one
      simp only [splayCost, ArticleMacro.kinds, ArticleMacro.requests, List.length_cons, List.length_nil,
        transcript.transcript.count_zigZig, transcript.transcript.count_zigZag]
      omega

end MultiSplay.MacroGeometry
