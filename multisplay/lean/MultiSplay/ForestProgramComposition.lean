import MultiSplay.ForestSplayNormalForm

/-! # Context and concatenation for the portable physical forest program -/

namespace MultiSplay.Unlocated

open Splay.Interface (Parameters)

variable {params : Parameters} {slack depth : Nat}

def Move.rightContext {before after : List Trees} (move : Move params slack depth before after) (context : List Trees) :
    Move params slack depth (before++context) (after++context) := by
  cases move with
  | request comparison before after key tail root execution cap normal =>
      exact .request comparison before after key (tail++context) root execution cap normal
  | rotation before after splay tail rotation normal => exact .rotation before after splay (tail++context) rotation normal
  | split left right sl sr tail => exact .split left right sl sr (tail++context)
  | join left right sl sr tail growing valueCap => exact .join left right sl sr (tail++context) growing valueCap
  | reorder order => exact .reorder (order.append_right context)

theorem Move.rightContext_counts {before after : List Trees} (move : Move params slack depth before after) (context : List Trees) :
    (move.rightContext context).splayCost = move.splayCost ∧
    (move.rightContext context).requests = move.requests ∧
    (move.rightContext context).rotations = move.rotations ∧
    (move.rightContext context).boundaries = move.boundaries ∧
    (move.rightContext context).comparisonCost = move.comparisonCost := by
  cases move <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def Program.append : {first middle last : List Trees} → Program params slack depth first middle →
    Program params slack depth middle last → Program params slack depth first last
  | _, _, _, .done _, later => later
  | _, _, _, .next head tail, later => .next head (tail.append later)

theorem Program.sum_append (charge : ∀ {before after}, Move params slack depth before after → Nat)
    {first middle last : List Trees} (early : Program params slack depth first middle) (late : Program params slack depth middle last) :
    (early.append late).sum charge = early.sum charge + late.sum charge := by
  induction early with
  | done => simp [append, sum]
  | next head tail ih => simp [append, sum, ih, Nat.add_assoc]

def Program.rightContext : {before after : List Trees} → Program params slack depth before after →
    (context : List Trees) → Program params slack depth (before++context) (after++context)
  | _, _, .done _, context => .done _
  | _, _, .next head tail, context => .next (head.rightContext context) (tail.rightContext context)

theorem Program.rightContext_counts {before after : List Trees} (program : Program params slack depth before after) (context : List Trees) :
    (program.rightContext context).splayCost = program.splayCost ∧
    (program.rightContext context).requests = program.requests ∧
    (program.rightContext context).rotations = program.rotations ∧
    (program.rightContext context).boundaries = program.boundaries ∧
    (program.rightContext context).comparisonCost = program.comparisonCost := by
  induction program with
  | done => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | next head tail ih =>
      obtain ⟨hc, hq, hr, hb, hw⟩ := head.rightContext_counts context
      exact ⟨congrArg₂ Nat.add hc ih.1, congrArg₂ Nat.add hq ih.2.1, congrArg₂ Nat.add hr ih.2.2.1,
        congrArg₂ Nat.add hb ih.2.2.2.1, congrArg₂ Nat.add hw ih.2.2.2.2⟩

/-- Component selection is a pure permutation. All selected local histories
and all unrelated surrounding components are retained. -/
theorem Program.context {before after : List Trees} (program : Program params slack depth before after) (front back : List Trees) :
    ∃ result : Program params slack depth (front++before++back) (front++after++back),
      result.splayCost = program.splayCost ∧ result.requests = program.requests ∧
      result.rotations = program.rotations ∧ result.boundaries = program.boundaries ∧ result.comparisonCost = program.comparisonCost := by
  have first : (front++before++back).Perm (before++(back++front)) := by
    simpa only [List.append_assoc] using (List.perm_append_comm : (front++(before++back)).Perm ((before++back)++front))
  have last : (after++(back++front)).Perm (front++after++back) := by
    simpa only [List.append_assoc] using (List.perm_append_comm : ((after++back)++front).Perm (front++(after++back)))
  let result : Program params slack depth (front++before++back) (front++after++back) :=
    .next (.reorder first) ((program.rightContext (back++front)).append (.next (.reorder last) (.done _)))
  have counted := program.rightContext_counts (back++front)
  refine ⟨result, ?_⟩
  simpa only [result, splayCost, requests, rotations, boundaries, comparisonCost, sum, sum_append,
    Move.splayCost, Move.requests, Move.rotations, Move.boundaries, Move.comparisonCost, Nat.add_zero, Nat.zero_add] using counted

end MultiSplay.Unlocated
