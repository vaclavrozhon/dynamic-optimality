import MultiSplay.ForestLocations

/-! # Every physical move has a persistent placement, including arbitrary joins -/

noncomputable section

namespace MultiSplay.Unlocated

open Splay.Interface (Element Parameters)

variable {m limit : Nat} {params : Parameters} {slack depth : Nat}

theorem Move.place {before after : List Trees} (move : Move params slack depth before after)
    (placement : Placement m limit before) (fits : limit + move.joins ≤ 2*m+1) :
    ∃ result : Placement m (limit+move.joins) after,
      ∃ step : PackedSplay.Move params slack depth (placement.locations.map Location.packed) (result.locations.map Location.packed),
        step.splayCost = move.splayCost ∧ step.requests = move.requests ∧
        step.rotations = move.rotations ∧ step.boundaries = move.boundaries := by
  rcases placement with ⟨locations, shapes, separate, bounded⟩
  cases move with
  | request comparison before after key tail root execution cap normal =>
      obtain ⟨element, rest, rfl, tailEq⟩ := locations_cons shapes
      let result : Placement m limit (⟨_, comparison, after⟩ :: tail) :=
        ⟨⟨⟨_, comparison, after⟩, element⟩ :: rest, by simp [tailEq],
          by simpa only [List.pairwise_cons, Location.Disjoint] using separate,
          by
            intro location member x
            rcases List.mem_cons.mp member with rfl | member
            · exact bounded _ (List.mem_cons_self) x
            · exact bounded location (List.mem_cons_of_mem _ member) x⟩
      exact ⟨result, .request comparison before after key element element.injective (rest.map Location.packed)
        root execution cap normal, rfl, rfl, rfl, rfl⟩
  | rotation before after splay tail rotation normal =>
      obtain ⟨element, rest, rfl, tailEq⟩ := locations_cons shapes
      let result : Placement m limit (⟨_, after, splay⟩ :: tail) :=
        ⟨⟨⟨_, after, splay⟩, element⟩ :: rest, by simp [tailEq],
          by simpa only [List.pairwise_cons, Location.Disjoint] using separate,
          by
            intro location member x
            rcases List.mem_cons.mp member with rfl | member
            · exact bounded _ (List.mem_cons_self) x
            · exact bounded location (List.mem_cons_of_mem _ member) x⟩
      exact ⟨result, .rotation before after splay element element.injective (rest.map Location.packed)
        rotation normal, rfl, rfl, rfl, rfl⟩
  | @split l r left right sl sr tail =>
      obtain ⟨element, rest, rfl, tailEq⟩ := locations_cons shapes
      let a : Element l ↪ Element m :=
        ⟨element ∘ JoinIntervals.leftEmbedding l r, element.injective.comp (RankEmbedding.external_injective _ _)⟩
      let b : Element r ↪ Element m :=
        ⟨element ∘ JoinIntervals.rightEmbedding l r, element.injective.comp (RankEmbedding.external_injective _ _)⟩
      have others := (List.pairwise_cons.mp separate).1
      have childSeparate : Location.Disjoint (⟨⟨l, left, sl⟩, a⟩ : Location m) ⟨⟨r, right, sr⟩, b⟩ :=
        fun x y same => JoinIntervals.disjoint l r x y (element.injective same)
      let result : Placement m limit (⟨l, left, sl⟩ :: ⟨r, right, sr⟩ :: tail) :=
        ⟨⟨⟨l, left, sl⟩, a⟩ :: ⟨⟨r, right, sr⟩, b⟩ :: rest, by simp [tailEq],
          List.pairwise_cons.mpr ⟨by
            intro location member
            rcases List.mem_cons.mp member with rfl | member
            · exact childSeparate
            · exact fun x y => others location member (JoinIntervals.leftEmbedding l r x) y,
          List.pairwise_cons.mpr ⟨fun location member x y => others location member (JoinIntervals.rightEmbedding l r x) y,
            (List.pairwise_cons.mp separate).2⟩⟩,
          by
            intro location member x
            rcases List.mem_cons.mp member with rfl | member
            · exact bounded _ (List.mem_cons_self) (JoinIntervals.leftEmbedding l r x)
            · rcases List.mem_cons.mp member with rfl | member
              · exact bounded _ (List.mem_cons_self) (JoinIntervals.rightEmbedding l r x)
              · exact bounded location (List.mem_cons_of_mem _ member) x⟩
      exact ⟨result, .split left right sl sr element element.injective (rest.map Location.packed), rfl, rfl, rfl, rfl⟩
  | @join l r left right sl sr tail growing valueCap =>
      dsimp only [Move.joins, Move.splayCost, Move.requests, Move.rotations, Move.boundaries] at fits ⊢
      obtain ⟨a, rest, rfl, restEq⟩ := locations_cons shapes
      obtain ⟨b, rest, rfl, tailEq⟩ := locations_cons restEq
      have aBound : ∀ x, (a x).val < limit := fun x => bounded _ (List.mem_cons_self) x
      have bBound : ∀ x, (b x).val < limit := fun x => bounded _ (List.mem_cons_of_mem _ (List.mem_cons_self)) x
      have tailBound : LocatedBelow limit rest :=
        fun location member x => bounded location (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)) x
      have firstSeparate := (List.pairwise_cons.mp separate).1
      have secondSeparate := (List.pairwise_cons.mp (List.pairwise_cons.mp separate).2).1
      let fresh : Element m := ⟨limit, by change limit+1 ≤ 2*m+1 at fits; omega⟩
      have aFree : ∀ x, a x ≠ fresh := by
        intro x same
        have h := congrArg Fin.val same
        have bound := aBound x
        change (a x).val = limit at h
        omega
      have bFree : ∀ x, b x ≠ fresh := by
        intro x same
        have h := congrArg Fin.val same
        have bound := bBound x
        change (b x).val = limit at h
        omega
      let parent : Element (0+l+1+r) ↪ Element m :=
        ⟨JoinLocation.element a b fresh, JoinLocation.injective a b fresh a.injective b.injective
          (firstSeparate _ (List.mem_cons_self)) aFree bFree⟩
      have parentSeparate : ∀ location ∈ rest, ∀ x y, parent x ≠ location.2 y := by
        intro location member
        apply JoinLocation.separate a b fresh location.2
        · exact firstSeparate location (List.mem_cons_of_mem _ member)
        · exact secondSeparate location member
        · intro y same
          have h := congrArg Fin.val same
          have bound := tailBound location member y
          change limit = (location.2 y).val at h
          omega
      let result : Placement m (limit+1) (⟨_, JoinRanks.tree left right, JoinRanks.tree sl sr⟩ :: tail) :=
        ⟨⟨⟨_, JoinRanks.tree left right, JoinRanks.tree sl sr⟩, parent⟩ :: rest, by simp [tailEq],
          List.pairwise_cons.mpr ⟨parentSeparate, (List.pairwise_cons.mp (List.pairwise_cons.mp separate).2).2⟩,
          by
            intro location member x
            rcases List.mem_cons.mp member with rfl | member
            · exact JoinLocation.bounded a b fresh (limit+1)
                (fun x => (aBound x).trans_le (Nat.le_succ _))
                (fun x => (bBound x).trans_le (Nat.le_succ _)) (Nat.lt_succ_self _) x
            · exact (tailBound location member x).trans_le (Nat.le_succ _)⟩
      refine ⟨result, ?_⟩
      have leftMap : (⟨parent ∘ JoinIntervals.leftEmbedding l r,
          parent.injective.comp (RankEmbedding.external_injective _ _)⟩ : Element l ↪ Element m) = a :=
        Function.Embedding.ext (JoinLocation.left a b fresh)
      have rightMap : (⟨parent ∘ JoinIntervals.rightEmbedding l r,
          parent.injective.comp (RankEmbedding.external_injective _ _)⟩ : Element r ↪ Element m) = b :=
        Function.Embedding.ext (JoinLocation.right a b fresh)
      have leftEq := congrArg (fun e : Element l ↪ Element m =>
        (⟨l, left, sl, e, e.injective⟩ : PackedSplay.Trees m)) leftMap
      have rightEq := congrArg (fun e : Element r ↪ Element m =>
        (⟨r, right, sr, e, e.injective⟩ : PackedSplay.Trees m)) rightMap
      have regionSeparate : ∀ trees ∈ rest.map Location.packed, ∀ x y, parent x ≠ trees.element y := by
        intro trees member
        obtain ⟨location, present, rfl⟩ := List.mem_map.mp member
        exact parentSeparate location present
      have joined : ∃ step : PackedSplay.Move params slack depth
          (⟨l, left, sl, parent ∘ JoinIntervals.leftEmbedding l r,
            parent.injective.comp (RankEmbedding.external_injective _ _)⟩ ::
           ⟨r, right, sr, parent ∘ JoinIntervals.rightEmbedding l r,
            parent.injective.comp (RankEmbedding.external_injective _ _)⟩ :: rest.map Location.packed)
          (⟨_, JoinRanks.tree left right, JoinRanks.tree sl sr, parent, parent.injective⟩ :: rest.map Location.packed),
          step.splayCost = 0 ∧ step.requests = 0 ∧ step.rotations = 0 ∧ step.boundaries = 1 :=
        ⟨.join left right sl sr parent parent.injective (rest.map Location.packed) regionSeparate growing valueCap,
          rfl, rfl, rfl, rfl⟩
      have sourceEq :
          (⟨l, left, sl, parent ∘ JoinIntervals.leftEmbedding l r,
            parent.injective.comp (RankEmbedding.external_injective _ _)⟩ ::
           ⟨r, right, sr, parent ∘ JoinIntervals.rightEmbedding l r,
            parent.injective.comp (RankEmbedding.external_injective _ _)⟩ :: rest.map Location.packed) =
          (⟨⟨l, left, sl⟩, a⟩ :: ⟨⟨r, right, sr⟩, b⟩ :: rest).map Location.packed :=
        congrArg₂ List.cons leftEq (congrArg₂ List.cons rightEq rfl)
      exact sourceEq ▸ joined
  | reorder order =>
      obtain ⟨result, localOrder, shapeEq⟩ := locations_perm (shapes ▸ order)
      let placed : Placement m limit _ :=
        ⟨result, shapeEq, localOrder.pairwise separate (fun h => h.symm),
          fun location member x => bounded location (localOrder.mem_iff.mpr member) x⟩
      exact ⟨placed, .reorder (localOrder.map Location.packed), rfl, rfl, rfl, rfl⟩

end MultiSplay.Unlocated
