import MultiSplay.ForestProgram
import MultiSplay.BoundarySwitch
import MultiSplay.ForestReflection

/-!
# Exact split/join checkpoints for the comparator

Once the actual pivot and existing ancestor guards are exposed, these
programs execute the prescribed classical switch word. They use only root
splits, raw joins and component permutations. The old tail remains in its
component until its prescribed split, including when a tail is empty.
-/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder)

variable {α : Type*}

theorem rotation_mirror {depth : Nat} {before after : RawTree α}
    (step : Rotation depth before after) :
    Rotation depth (Auxiliary.mirror before) (Auxiliary.mirror after) := by
  induction step with
  | right a b c x y => exact .left _ _ _ _ _
  | left a b c x y => exact .right _ _ _ _ _
  | leftContext step key right ih => exact .rightContext _ key ih
  | rightContext left key step ih => exact .leftContext ih key _

/-- Reflection includes the necessary component permutations at split and
join checkpoints; it preserves the literal event order and total charge. -/
theorem Program.mirror {before after : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (program : Program before word after work) :
    Program (before.map Auxiliary.mirror) (word.map Event.mirror)
      (after.map Auxiliary.mirror) work := by
  apply Trace.mirror (access := RootAccess) (prepare := RotationPreparation) ?_ ?_ program
  · intro key a b cost access
    cases access
    exact .root _ _ _
  · intro a b cost preparation
    obtain ⟨depth, step, rfl⟩ := preparation
    exact ⟨depth, rotation_mirror step, rfl⟩

theorem leftToRight_checkpoints (a old incoming b : RawTree α) (lower pivot upper : α) :
    Program [.node (.node a lower old) pivot (.node .empty upper b), incoming]
      (leftToRightWord (inorder a) (inorder old) (inorder incoming) (inorder b) lower pivot upper)
      [.node (.node a lower .empty) pivot (.node incoming upper b), old] 6 := by
  have first : Program [(.node (.node a lower old) pivot (.node .empty upper b)), incoming]
      [.split (inorder (.node a lower old)) pivot (inorder (.node .empty upper b))] [(.node a lower old), (.node .empty upper b), incoming] (0 + 1) := by
    simpa using (Trace.single (Step.split (RootAccess.root (.node a lower old) pivot (.node .empty upper b)))).context [] [incoming]
  have second : Program [(.node a lower old), (.node .empty upper b), incoming]
      [.split (inorder a) lower (inorder old)] [a, old, (.node .empty upper b), incoming] (0 + 1) := by
    simpa using (Trace.single (Step.split (RootAccess.root a lower old))).context [] [(.node .empty upper b), incoming]
  have third : Program [a, old, (.node .empty upper b), incoming]
      [.split [] upper (inorder b)] [a, old, .empty, b, incoming] (0 + 1) := by
    simpa [inorder] using (Trace.single (Step.split (RootAccess.root .empty upper b))).context [a, old] [incoming]
  have order : ([a, old, .empty, b, incoming] : List (RawTree α)).Perm
      [a, .empty, incoming, b, old] := by
    have firstOrder : ([old, .empty, b, incoming] : List (RawTree α)).Perm
        [.empty, b, incoming, old] := by
      simpa using (List.perm_middle : ([.empty, b, incoming] ++ [old]).Perm
        (old :: [.empty, b, incoming])).symm
    have secondOrder : ([.empty, b, incoming, old] : List (RawTree α)).Perm
        [.empty, incoming, b, old] :=
      List.Perm.cons .empty (List.Perm.swap incoming b [old])
    exact List.Perm.cons a (firstOrder.trans secondOrder)
  have fourth : Program [a, .empty, incoming, b, old]
      [.join (inorder a) lower []] [.node a lower .empty, incoming, b, old] 1 := by
    simpa [inorder] using (Trace.single (Step.join a .empty lower)).context [] [incoming, b, old]
  have fifth : Program [.node a lower .empty, incoming, b, old]
      [.join (inorder incoming) upper (inorder b)]
      [.node a lower .empty, .node incoming upper b, old] 1 := by
    simpa using (Trace.single (Step.join incoming b upper)).context [.node a lower .empty] [old]
  have sixth : Program [.node a lower .empty, .node incoming upper b, old]
      [.join (inorder (.node a lower .empty)) pivot (inorder (.node incoming upper b))]
      [.node (.node a lower .empty) pivot (.node incoming upper b), old] 1 := by
    simpa using (Trace.single (Step.join (.node a lower .empty) (.node incoming upper b) pivot)).context [] [old]
  have total := first.append (second.append (third.append
    ((Trace.single (Step.reorder order)).append (fourth.append (fifth.append sixth)))))
  simpa [leftToRightWord, inorder, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using total

theorem noLower_checkpoints (old incoming b : RawTree α) (pivot upper : α) :
    Program [.node old pivot (.node .empty upper b), incoming]
      (noLowerWord (inorder old) (inorder incoming) (inorder b) pivot upper)
      [.node .empty pivot (.node incoming upper b), old] 4 := by
  have first : Program [(.node old pivot (.node .empty upper b)), incoming]
      [.split (inorder old) pivot (inorder (.node .empty upper b))] [old, (.node .empty upper b), incoming] (0 + 1) := by
    simpa using (Trace.single (Step.split (RootAccess.root old pivot (.node .empty upper b)))).context [] [incoming]
  have second : Program [old, (.node .empty upper b), incoming]
      [.split [] upper (inorder b)] [old, .empty, b, incoming] (0 + 1) := by
    simpa [inorder] using (Trace.single (Step.split (RootAccess.root .empty upper b))).context [old] [incoming]
  have firstOrder : ([old, .empty, b, incoming] : List (RawTree α)).Perm [.empty, b, incoming, old] := by
    simpa using (List.perm_middle : ([.empty, b, incoming] ++ [old]).Perm (old :: [.empty, b, incoming])).symm
  have secondOrder : ([.empty, b, incoming, old] : List (RawTree α)).Perm [.empty, incoming, b, old] :=
    List.Perm.cons .empty (List.Perm.swap incoming b [old])
  have third : Program [.empty, incoming, b, old]
      [.join (inorder incoming) upper (inorder b)] [.empty, .node incoming upper b, old] 1 := by
    simpa using (Trace.single (Step.join incoming b upper)).context [.empty] [old]
  have fourth : Program [.empty, .node incoming upper b, old]
      [.join [] pivot (inorder (.node incoming upper b))] [.node .empty pivot (.node incoming upper b), old] 1 := by
    simpa [inorder] using (Trace.single (Step.join .empty (.node incoming upper b) pivot)).context [] [old]
  have total := first.append (second.append
    ((Trace.single (Step.reorder (firstOrder.trans secondOrder))).append (third.append fourth)))
  simpa [noLowerWord, inorder, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using total

theorem noUpper_checkpoints (a old incoming : RawTree α) (lower pivot : α) :
    Program [.node (.node a lower old) pivot .empty, incoming]
      (noUpperWord (inorder a) (inorder old) (inorder incoming) lower pivot)
      [.node (.node a lower .empty) pivot incoming, old] 4 := by
  have first : Program [(.node (.node a lower old) pivot .empty), incoming]
      [.split (inorder (.node a lower old)) pivot []] [(.node a lower old), .empty, incoming] (0 + 1) := by
    simpa [inorder] using (Trace.single (Step.split (RootAccess.root (.node a lower old) pivot .empty))).context [] [incoming]
  have second : Program [(.node a lower old), .empty, incoming]
      [.split (inorder a) lower (inorder old)] [a, old, .empty, incoming] (0 + 1) := by
    simpa using (Trace.single (Step.split (RootAccess.root a lower old))).context [] [.empty, incoming]
  have order : ([a, old, .empty, incoming] : List (RawTree α)).Perm [a, .empty, incoming, old] := by
    apply List.Perm.cons a
    simpa using (List.perm_middle : ([.empty, incoming] ++ [old]).Perm (old :: [.empty, incoming])).symm
  have third : Program [a, .empty, incoming, old]
      [.join (inorder a) lower []] [.node a lower .empty, incoming, old] 1 := by
    simpa [inorder] using (Trace.single (Step.join a .empty lower)).context [] [incoming, old]
  have fourth : Program [.node a lower .empty, incoming, old]
      [.join (inorder (.node a lower .empty)) pivot (inorder incoming)]
      [.node (.node a lower .empty) pivot incoming, old] 1 := by
    simpa using (Trace.single (Step.join (.node a lower .empty) incoming pivot)).context [] [old]
  have total := first.append (second.append ((Trace.single (Step.reorder order)).append (third.append fourth)))
  simpa [noUpperWord, inorder, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using total

theorem noGuards_checkpoints (old incoming : RawTree α) (pivot : α) :
    Program [.node old pivot .empty, incoming]
      (noGuardsWord (inorder old) (inorder incoming) pivot)
      [.node .empty pivot incoming, old] 2 := by
  have first : Program [(.node old pivot .empty), incoming]
      [.split (inorder old) pivot []] [old, .empty, incoming] (0 + 1) := by
    simpa [inorder] using (Trace.single (Step.split (RootAccess.root old pivot .empty))).context [] [incoming]
  have order : ([old, .empty, incoming] : List (RawTree α)).Perm [.empty, incoming, old] := by
    simpa using (List.perm_middle : ([.empty, incoming] ++ [old]).Perm (old :: [.empty, incoming])).symm
  have second : Program [.empty, incoming, old]
      [.join [] pivot (inorder incoming)] [.node .empty pivot incoming, old] 1 := by
    simpa [inorder] using (Trace.single (Step.join .empty incoming pivot)).context [] [old]
  simpa [noGuardsWord, Nat.add_assoc] using first.append ((Trace.single (Step.reorder order)).append second)

end MultiSplay.CommonForest
