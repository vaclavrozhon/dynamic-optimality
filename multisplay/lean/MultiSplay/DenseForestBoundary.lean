import MultiSplay.DenseForestComponent

/-! # Actual common split/join boundaries and their dense physical programs -/

namespace MultiSplay.DenseForest

open DynamicOptimality (RawTree)
open Splay.Accounting (articleParameters)
open Splay.Interface (Parameters)
open Splay.Tree (BST)

variable {α : Type*} {params : Parameters} {slack depth : Nat}

theorem split_root (component : Component α) (common : CommonRoot component.trees)
    {left right : RawTree α} {key : α} (root : component.source = .node left key right) :
    ∃ a b : Component α, a.source = left ∧ b.source = right ∧ component.actual = .node a.actual key b.actual ∧
      ∃ program : Unlocated.Program params slack depth [component.trees] [a.trees, b.trees],
        program.splayCost = 0 ∧ program.requests = 0 ∧ program.rotations = 0 ∧
        program.boundaries = 1 ∧ program.comparisonCost = 1 := by
  rcases component with ⟨trees, alphabet⟩
  obtain ⟨pivot, comparisonRoot, splayRoot⟩ := common
  obtain ⟨l, r, cl, cr, sl, sr, same⟩ := Unlocated.paired_root_decomposition trees.comparison trees.splay comparisonRoot splayRoot
  have treesEq : trees = ⟨_, JoinRanks.tree cl cr, JoinRanks.tree sl sr⟩ := same
  subst trees
  let a : Component α := ⟨⟨l, cl, sl⟩, alphabet⟩
  let b : Component α := ⟨⟨r, cr, sr⟩, fun index => alphabet (0+l+1+index)⟩
  change Auxiliary.map alphabet (DynamicOptimality.BST.toRaw (JoinRanks.tree cl cr)) = _ at root
  rw [Alphabet.joined_physical] at root
  obtain ⟨leftEq, keyEq, rightEq⟩ := ChaCha.MTR.Tree.node.inj root
  refine ⟨a, b, leftEq, rightEq, ?_, .next (.split cl cr sl sr []) (.done _), rfl, rfl, rfl, rfl, rfl⟩
  change Auxiliary.map alphabet (DynamicOptimality.BST.toRaw (JoinRanks.tree sl sr)) = _
  rw [Alphabet.joined_physical, keyEq]
  rfl

theorem join (a b : Component α) (key : α)
    (growing : 2 ≤ params.growingLimit) (cap : 3 ≤ params.valueBound) :
    ∃ result : Component α, result.source = .node a.source key b.source ∧ result.actual = .node a.actual key b.actual ∧
      ∃ program : Unlocated.Program params slack depth [a.trees, b.trees] [result.trees],
        program.splayCost = 0 ∧ program.requests = 0 ∧ program.rotations = 0 ∧
        program.boundaries = 1 ∧ program.comparisonCost = 1 := by
  let shiftedRight := fun index => b.alphabet (index - (0+a.trees.size+1))
  let alphabet := Alphabet.join (0+a.trees.size) key a.alphabet shiftedRight
  let result : Component α :=
    ⟨⟨_, JoinRanks.tree a.trees.comparison b.trees.comparison, JoinRanks.tree a.trees.splay b.trees.splay⟩, alphabet⟩
  have joined : ∀ (left : BST 0 a.trees.size) (right : BST 0 b.trees.size),
      Auxiliary.map alphabet (DynamicOptimality.BST.toRaw (JoinRanks.tree left right)) =
        .node (Auxiliary.map a.alphabet (DynamicOptimality.BST.toRaw left)) key
          (Auxiliary.map b.alphabet (DynamicOptimality.BST.toRaw right)) := by
    intro left right
    simp only [JoinRanks.tree, DynamicOptimality.BST.toRaw, Auxiliary.map, alphabet,
      Alphabet.join_left, Alphabet.join_root, Alphabet.join_right]
    have leftEq : Auxiliary.map a.alphabet (DynamicOptimality.BST.toRaw (OrdinalShift.tree 0 left)) =
        Auxiliary.map a.alphabet (DynamicOptimality.BST.toRaw left) := by
      simpa only [Nat.sub_zero] using OrdinalShift.tree_alphabet 0 left a.alphabet
    exact congrArg₂ (fun x y => ChaCha.MTR.Tree.node x key y) leftEq
      (OrdinalShift.tree_alphabet (0+a.trees.size+1) right b.alphabet)
  exact ⟨result, joined _ _, joined _ _, .next
    (.join a.trees.comparison b.trees.comparison a.trees.splay b.trees.splay [] growing cap) (.done _),
    rfl, rfl, rfl, rfl, rfl⟩

end MultiSplay.DenseForest
