import MultiSplay.PackedProgram

/-! # Constructing the complete shared history from the physical program -/

noncomputable section

namespace MultiSplay.PackedSplay

open Splay.Accounting
open Splay.Interface (Parameters)
open SharedSplay

variable {m : Nat} {params : Parameters} {slack depth : Nat}

theorem locals_cons {forest : List (Local m)} {head : Trees m} {tail : List (Trees m)}
    (same : forest.map Sigma.fst = head :: tail) :
    ∃ state : Splay.Lazy.State head.size, ∃ rest : List (Local m),
      forest = ⟨head, state⟩ :: rest ∧ rest.map Sigma.fst = tail := by
  cases forest with
  | nil => cases same
  | cons first rest =>
      obtain ⟨shapeEq, tailEq⟩ := List.cons.inj same
      rcases first with ⟨shape, state⟩
      dsimp only at shapeEq
      subst shape
      exact ⟨state, rest, rfl, tailEq⟩

theorem locals_perm {forest : List (Local m)} {after : List (Trees m)}
    (order : (forest.map Sigma.fst).Perm after) :
    ∃ result : List (Local m), forest.Perm result ∧ result.map Sigma.fst = after := by
  have lifted : Relation.Comp (fun a b => a = b.map Sigma.fst) List.Perm after forest := by
    rw [List.eq_map_comp_perm]
    exact order.symm
  obtain ⟨result, same, perm⟩ := lifted
  exact ⟨result, perm.symm, same.symm⟩

theorem Move.realize {before after : List (Trees m)} (move : Move params slack depth before after)
    (forest : List (Local m)) (whole : Splay.Interface.State m)
    (packing : Packing params forest whole) (shapes : forest.map Sigma.fst = before) :
    ∃ result : List (Local m), ∃ final : Splay.Interface.State m,
      Nonempty (Packing params result final) ∧ result.map Sigma.fst = after ∧
      ∃ segment : Segment params whole final,
        SegmentEvolution slack depth segment (geometry forest) (geometry result) ∧
        segment.splayCost = move.splayCost ∧ segment.requests = move.requests ∧
        segment.rotations = move.rotations ∧ segment.maintenanceCost ≤ 8 * move.boundaries := by
  cases move with
  | request comparison before after key element injective tail root execution cap normal =>
      obtain ⟨state, rest, rfl, tailEq⟩ := locals_cons shapes
      have cert := packing.certified _ (List.mem_cons_self)
      let transcript := splayExecutionTranscriptWitness execution
      obtain ⟨request⟩ := ArticleCompleteRequest.exists_of_transcript root transcript.transcript cert.represented cap
      let step : ArticleMacro params ⟨comparison, before, state⟩ ⟨comparison, after, request.final⟩ :=
        .request (before := ⟨comparison, before, state⟩) cert.represented root execution transcript request
      obtain ⟨final, newPacking, segment, evolution, cost, requests, rotations, maintenance⟩ :=
        article _ _ element injective rest whole packing step slack depth normal
      refine ⟨⟨⟨_, comparison, after, element, injective⟩, request.final⟩ :: rest, final, newPacking,
        by simpa only [List.map_cons, tailEq], segment, evolution, cost, requests, rotations, ?_⟩
      exact Nat.le_of_eq maintenance
  | rotation before after splay element injective tail rotation normal =>
      obtain ⟨state, rest, rfl, tailEq⟩ := locals_cons shapes
      have cert := packing.certified _ (List.mem_cons_self)
      obtain ⟨execution⟩ := ArticleComparisonExecution.exists_of_rotation rotation cert.represented
      let step : ArticleMacro params ⟨before, splay, state⟩ ⟨after, splay, execution.final⟩ :=
        .rotation (before := ⟨before, splay, state⟩) cert.represented rotation execution
      obtain ⟨final, newPacking, segment, evolution, cost, requests, rotations, maintenance⟩ :=
        article _ _ element injective rest whole packing step slack depth normal
      refine ⟨⟨⟨_, after, splay, element, injective⟩, execution.final⟩ :: rest, final, newPacking,
        by simpa only [List.map_cons, tailEq], segment, evolution, cost, requests, rotations, ?_⟩
      exact Nat.le_of_eq maintenance
  | split left right sl sr element injective tail =>
      obtain ⟨state, rest, rfl, tailEq⟩ := locals_cons shapes
      obtain ⟨a, b, final, newPacking, segment, evolution, cost, requests, rotations, maintenance⟩ :=
        PackedSplay.split left right sl sr element injective state rest whole packing slack depth
      refine ⟨_, final, newPacking, ?_, segment, evolution, cost, requests, rotations, maintenance⟩
      simp only [List.map_cons, tailEq]
  | join left right sl sr element injective tail disjoint growingLimit valueCap =>
      obtain ⟨a, rest, rfl, restEq⟩ := locals_cons shapes
      obtain ⟨b, rest, rfl, tailEq⟩ := locals_cons restEq
      have regionSeparate : ∀ component ∈ rest, ∀ x y, element x ≠ component.1.element y := by
        intro component member
        exact disjoint component.1 (tailEq ▸ List.mem_map.mpr ⟨component, member, rfl⟩)
      obtain ⟨state, final, newPacking, segment, evolution, cost, requests, rotations, maintenance⟩ :=
        PackedSplay.join left right sl sr element injective a b rest whole packing regionSeparate growingLimit valueCap slack depth
      refine ⟨_, final, newPacking, ?_, segment, evolution, cost, requests, rotations, maintenance⟩
      simp only [List.map_cons, tailEq]
  | reorder order =>
      obtain ⟨result, localOrder, shapeEq⟩ := locals_perm (shapes ▸ order)
      have actual := Splay.Interface.Trace.nil packing.valid
      refine ⟨result, whole, ⟨packing.reorder localOrder⟩, shapeEq, .maintenance actual,
        .maintenance actual (.reorder (localOrder.map _)), rfl, rfl, rfl, Nat.le_refl 0⟩

theorem Program.realize {before after : List (Trees m)} (program : Program params slack depth before after)
    (forest : List (Local m)) (whole : Splay.Interface.State m)
    (packing : Packing params forest whole) (shapes : forest.map Sigma.fst = before) :
    ∃ result : List (Local m), ∃ final : Splay.Interface.State m,
      Nonempty (Packing params result final) ∧ result.map Sigma.fst = after ∧
      ∃ history : History params whole final,
        Evolution slack depth history (geometry forest) (geometry result) ∧
        history.splayCost = program.splayCost ∧ history.requests = program.requests ∧
        history.rotations = program.rotations ∧ history.maintenanceCost ≤ 8 * program.boundaries := by
  induction program generalizing forest whole with
  | done before =>
      exact ⟨forest, whole, ⟨packing⟩, shapes, .done whole, .done whole (geometry forest), rfl, rfl, rfl, Nat.le_refl 0⟩
  | next move tail ih =>
      obtain ⟨middle, middleGlobal, ⟨middlePacking⟩, middleEq, segment, headEvolution,
        headCost, headRequests, headRotations, headMaintenance⟩ := move.realize forest whole packing shapes
      obtain ⟨result, final, finalPacking, finalEq, history, tailEvolution,
        tailCost, tailRequests, tailRotations, tailMaintenance⟩ := ih middle middleGlobal middlePacking middleEq
      refine ⟨result, final, finalPacking, finalEq, .next segment history,
        .next headEvolution tailEvolution, ?_, ?_, ?_, ?_⟩
      · exact congrArg₂ Nat.add headCost tailCost
      · exact congrArg₂ Nat.add headRequests tailRequests
      · exact congrArg₂ Nat.add headRotations tailRotations
      · change segment.maintenanceCost + history.maintenanceCost ≤ 8 * (move.boundaries + tail.boundaries)
        omega

end MultiSplay.PackedSplay
