import MultiSplay.UnlocatedProgram
import MultiSplay.JoinLocation
import MultiSplay.PackedInitialization

/-! # Disjoint persistent locations and a finite fresh-slot budget -/

namespace MultiSplay.Unlocated

open Splay.Interface (Element)

abbrev Location (m : Nat) := Sigma (fun trees : Trees => Element trees.size ↪ Element m)

variable {m : Nat}

def Location.packed (location : Location m) : PackedSplay.Trees m :=
  ⟨location.1.size, location.1.comparison, location.1.splay, location.2, location.2.injective⟩

def Location.Disjoint (a b : Location m) : Prop := ∀ x y, a.2 x ≠ b.2 y

theorem Location.Disjoint.symm {a b : Location m} (separate : a.Disjoint b) : b.Disjoint a :=
  fun x y => (separate y x).symm

def LocatedBelow (limit : Nat) (locations : List (Location m)) : Prop :=
  ∀ location ∈ locations, ∀ x, (location.2 x).val < limit

structure Placement (m limit : Nat) (forest : List Trees) where
  locations : List (Location m)
  shapes : locations.map Sigma.fst = forest
  separate : locations.Pairwise Location.Disjoint
  bounded : LocatedBelow limit locations

theorem packed_separate (locations : List (Location m)) (separate : locations.Pairwise Location.Disjoint) :
    (locations.map Location.packed).Pairwise PackedSplay.Trees.Disjoint := by
  rw [List.pairwise_map]
  exact separate

theorem packed_mass (locations : List (Location m)) :
    PackedSplay.Trees.mass (locations.map Location.packed) = mass (locations.map Sigma.fst) := by
  simp only [PackedSplay.Trees.mass, mass, List.map_map, Function.comp_def, Location.packed]

theorem locations_cons {locations : List (Location m)} {head : Trees} {tail : List Trees}
    (same : locations.map Sigma.fst = head :: tail) :
    ∃ element : Element head.size ↪ Element m, ∃ rest : List (Location m),
      locations = ⟨head, element⟩ :: rest ∧ rest.map Sigma.fst = tail := by
  cases locations with
  | nil => cases same
  | cons first rest =>
      obtain ⟨shapeEq, tailEq⟩ := List.cons.inj same
      rcases first with ⟨shape, element⟩
      dsimp only at shapeEq
      subst shape
      exact ⟨element, rest, rfl, tailEq⟩

theorem locations_perm {locations : List (Location m)} {after : List Trees}
    (order : (locations.map Sigma.fst).Perm after) :
    ∃ result : List (Location m), locations.Perm result ∧ result.map Sigma.fst = after := by
  have lifted : Relation.Comp (fun a b => a = b.map Sigma.fst) List.Perm after locations := by
    rw [List.eq_map_comp_perm]
    exact order.symm
  obtain ⟨result, same, perm⟩ := lifted
  exact ⟨result, perm.symm, same.symm⟩

theorem allocate (forest : List Trees) (offset : Nat) (fits : offset + mass forest ≤ 2*m+1) :
    ∃ locations : List (Location m), locations.map Sigma.fst = forest ∧ locations.Pairwise Location.Disjoint ∧
      ∀ location ∈ locations, ∀ x, offset ≤ (location.2 x).val ∧ (location.2 x).val < offset + mass forest := by
  induction forest generalizing offset with
  | nil => exact ⟨[], rfl, .nil, by intro location member; cases member⟩
  | cons head tail ih =>
      have size : mass (head :: tail) = (2*head.size+1) + mass tail := rfl
      let element : Element head.size ↪ Element m :=
        ⟨fun x => ⟨offset+x.val, by have bound := x.isLt; rw [size] at fits; omega⟩,
          by intro x y same; apply Fin.ext; have values := congrArg Fin.val same; dsimp only at values; omega⟩
      obtain ⟨rest, shapes, separate, bounds⟩ := ih (offset+2*head.size+1) (by rw [size] at fits; omega)
      refine ⟨⟨head, element⟩ :: rest, by simp [shapes], List.pairwise_cons.mpr ⟨?_, separate⟩, ?_⟩
      · intro location member x y same
        have limit := (bounds location member y).1
        have first := x.isLt
        change x.val < 2*head.size+1 at first
        have values := congrArg Fin.val same
        change offset+x.val = (location.2 y).val at values
        omega
      · intro location member x
        rcases List.mem_cons.mp member with rfl | member
        · change offset ≤ offset+x.val ∧ offset+x.val < offset+mass (head::tail)
          have bound := x.isLt
          change x.val < 2*head.size+1 at bound
          rw [size]
          omega
        · have bound := bounds location member x
          rw [size]
          omega

theorem initial_placement (forest : List Trees) (fits : mass forest ≤ 2*m+1) :
    Nonempty (Placement m (mass forest) forest) := by
  obtain ⟨locations, shapes, separate, bounded⟩ := allocate forest 0 (by simpa using fits)
  exact ⟨⟨locations, shapes, separate, fun location member x => by simpa using (bounded location member x).2⟩⟩

end MultiSplay.Unlocated
