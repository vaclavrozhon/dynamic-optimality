import MultiSplay.ComparatorGuardProjection
import MultiSplay.ComparatorForestInitialization

/-! # Framing a component while an opaque exit changes

Only the current preferred path determines its physical projection. The
preference state inside an off-path subtree may change arbitrarily without
changing the projected component, provided its endpoint remains the same.
-/

namespace MultiSplay.ComparatorPrimary

open DynamicOptimality ChaCha Paper20261030
open EndpointEncoding ColoredStorage PrimaryWings PreferredProjection
open ComparatorGuard

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def signature (primary : PrefRouter Nat) : List (Bool × Nat) :=
  (exits primary).map (fun exit => (exit.leftOfEndpoint,lastGap exit.subtree))

theorem signature_finish {lower upper : Nat} (reference : BST lower upper)
    (before after : State)
    (same : ComparatorForest.finish before reference.toRaw = ComparatorForest.finish after reference.toRaw) :
    signature (routing before reference) = signature (routing after reference) ∧
      (routing before reference).terminal = (routing after reference).terminal := by
  induction reference generalizing before after with
  | empty => exact ⟨rfl,rfl⟩
  | node left right ihl ihr =>
      cases old : before [] <;> cases fresh : after []
      · have child := List.cons.inj (by simpa only [DynamicOptimality.BST.toRaw,
          ComparatorForest.finish,old,fresh,Bool.false_eq_true,if_false] using same)
        obtain ⟨ports,terminal⟩ := ihl (below before false) (below after false) child.2
        simp only [signature] at ports
        simp [routing,old,fresh,signature,exits,lastGap_routing,PrefRouter.terminal,ports,terminal]
      · simp [DynamicOptimality.BST.toRaw,ComparatorForest.finish,old,fresh] at same
      · simp [DynamicOptimality.BST.toRaw,ComparatorForest.finish,old,fresh] at same
      · have child := List.cons.inj (by simpa only [DynamicOptimality.BST.toRaw,
          ComparatorForest.finish,old,fresh,if_true] using same)
        obtain ⟨ports,terminal⟩ := ihr (below before true) (below after true) child.2
        simp only [signature] at ports
        simp [routing,old,fresh,signature,exits,lastGap_routing,PrefRouter.terminal,ports,terminal]

private theorem portAt_map {α β : Type*} (f : α → β) (start depth : Nat) (ports : List α) :
    portAt start (ports.map f) depth = (portAt start ports depth).map f := by
  unfold portAt
  split <;> simp [List.getElem?_map]

private theorem port_signature {first second : PrefRouter Nat} (same : signature first = signature second)
    (start depth : Nat) :
    (portAt start (exits first) depth).map (fun exit => (exit.leftOfEndpoint,lastGap exit.subtree)) =
    (portAt start (exits second) depth).map (fun exit => (exit.leftOfEndpoint,lastGap exit.subtree)) := by
  rw [← portAt_map,← portAt_map]
  exact congrArg (fun ports => portAt start ports depth) same

private theorem color_signature {first second : PrefRouter Nat} (same : signature first = signature second)
    (start : Nat) : PackedPrimary.color start first = PackedPrimary.color start second := by
  funext depth
  have ports := port_signature same start depth
  have colors := congrArg (Option.map Prod.fst) ports
  simpa only [Option.map_map,Function.comp_def,PackedPrimary.color] using colors

private theorem label_signature {lower upper : Nat} (reference : BST lower upper)
    (before after : State) (same : signature (routing before reference) = signature (routing after reference))
    (start : Nat) :
    (fun depth => lastGap (PackedPrimary.label start (routing before reference) depth).subtree) =
    (fun depth => lastGap (PackedPrimary.label start (routing after reference) depth).subtree) := by
  funext depth
  have ports := port_signature same start depth
  unfold PackedPrimary.label
  cases first : portAt start (exits (routing before reference)) depth <;>
    cases second : portAt start (exits (routing after reference)) depth <;>
    simp_all only [Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
      Option.some.injEq,Prod.mk.injEq,lastGap_routing,reduceCtorEq]

/-- The endpoint fixes the complete selected path, but does not fix the
preference states inside its opaque nonpreferred subtrees. -/
theorem projectedTree_state_congr {lower upper : Nat} {ρ : Type*}
    (reference : BST lower upper) (before after : State)
    (same : ComparatorForest.finish before reference.toRaw = ComparatorForest.finish after reference.toRaw)
    (start : Nat) (source : Source Nat ρ) :
    projectedTree before reference start source = projectedTree after reference start source := by
  obtain ⟨ports,terminal⟩ := signature_finish reference before after same
  have colors := color_signature ports start
  have labels := label_signature reference before after ports start
  rw [projectedTree_blocks,projectedTree_blocks]
  simp only [boundaryWing,colors,labels,terminal]

end MultiSplay.ComparatorPrimary
