import MultiSplay.OrdinalDense
import MultiSplay.ForestProgramComposition

/-! # Exact dense child coordinates at a common comparison/splay root -/

namespace MultiSplay.Unlocated

open Splay.Tree (BST)

theorem paired_root_decomposition {n key : Nat} (comparison splay : BST 0 n)
    (comparisonRoot : comparison.HasRoot key) (splayRoot : splay.HasRoot key) :
    ∃ l r : Nat, ∃ cl : BST 0 l, ∃ cr : BST 0 r, ∃ sl : BST 0 l, ∃ sr : BST 0 r,
      (⟨n, comparison, splay⟩ : Trees) =
        ⟨0+l+1+r, JoinRanks.tree cl cr, JoinRanks.tree sl sr⟩ := by
  obtain ⟨cl, cr, rfl⟩ := comparisonRoot
  obtain ⟨sl, sr, rfl⟩ := splayRoot
  obtain ⟨l, cl', leftSize, leftEq⟩ := Alphabet.exists_unshift cl
  obtain ⟨r, cr', rightSize, rightEq⟩ := Alphabet.exists_unshift cr
  obtain ⟨ls, sl', leftSplaySize, leftSplayEq⟩ := Alphabet.exists_unshift sl
  obtain ⟨rs, sr', rightSplaySize, rightSplayEq⟩ := Alphabet.exists_unshift sr
  have sameLeft : ls = l := by omega
  have sameRight : rs = r := by omega
  subst ls rs
  clear leftSplaySize rightSplaySize
  subst key n
  have lc := eq_of_heq leftEq
  have rc := eq_of_heq rightEq
  have ls := eq_of_heq leftSplayEq
  have rs := eq_of_heq rightSplayEq
  refine ⟨l, r, cl', cr', sl', sr', ?_⟩
  rw [← lc, ← rc, ← ls, ← rs]
  rfl

end MultiSplay.Unlocated

namespace MultiSplay.Alphabet

open Splay.Tree (BST)

theorem map_comp (first : α → β) (second : β → γ) (source : DynamicOptimality.RawTree α) :
    Auxiliary.map second (Auxiliary.map first source) = Auxiliary.map (second ∘ first) source := by
  induction source <;> simp_all [Auxiliary.map, Function.comp_def]

theorem joined_physical {l r : Nat} (left : BST 0 l) (right : BST 0 r) (alphabet : Nat → α) :
    Auxiliary.map alphabet (DynamicOptimality.BST.toRaw (JoinRanks.tree left right)) =
      .node (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw left)) (alphabet (0+l))
        (Auxiliary.map (fun key => alphabet (0+l+1+key)) (DynamicOptimality.BST.toRaw right)) := by
  simp only [JoinRanks.tree, DynamicOptimality.BST.toRaw, Auxiliary.map, OrdinalShift.toRaw, map_comp]
  congr 1
  apply indexed_congr
  intro key _ _
  simp

end MultiSplay.Alphabet
