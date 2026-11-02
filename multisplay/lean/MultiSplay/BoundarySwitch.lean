import MultiSplay.CommonForest

/-! Exact standard switches when one or both ancestor guards are absent.
The empty components are real empty child domains, not extra physical keys. -/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder)

variable {α : Type*}

def noLowerWord (old incoming b : List α) (pivot upper : α) : List (Event α) :=
  [.split old pivot ([upper] ++ b), .split [] upper b,
   .join incoming upper b, .join [] pivot (incoming ++ [upper] ++ b)]

def noUpperWord (a old incoming : List α) (lower pivot : α) : List (Event α) :=
  [.split (a ++ [lower] ++ old) pivot [], .split a lower old,
   .join a lower [], .join (a ++ [lower]) pivot incoming]

def noGuardsWord (old incoming : List α) (pivot : α) : List (Event α) :=
  [.split old pivot [], .join [] pivot incoming]

theorem noLowerWord_structural (old incoming b : List α) (pivot upper : α) :
    structuralCount (noLowerWord old incoming b pivot upper) = 4 := by
  simp [structuralCount, noLowerWord, Event.structural]

theorem noUpperWord_structural (a old incoming : List α) (lower pivot : α) :
    structuralCount (noUpperWord a old incoming lower pivot) = 4 := by
  simp [structuralCount, noUpperWord, Event.structural]

theorem noGuardsWord_structural (old incoming : List α) (pivot : α) :
    structuralCount (noGuardsWord old incoming pivot) = 2 := by
  simp [structuralCount, noGuardsWord, Event.structural]

theorem noLower_exact {whole old right incoming b : RawTree α}
    {pivot upper : α} {pivotWork rightWork : Nat}
    (pivotSplay : Auxiliary.Splay pivot whole (.node old pivot right) pivotWork)
    (rightSplay : Auxiliary.Splay upper right (.node .empty upper b) rightWork) :
    SplayTrace [whole, incoming] (noLowerWord (inorder old) (inorder incoming) (inorder b) pivot upper)
      [.node .empty pivot (.node incoming upper b), old] (pivotWork + rightWork + 4) := by
  have first : SplayTrace [whole, incoming]
      [.split (inorder old) pivot (inorder right)] [old, right, incoming] (pivotWork + 1) := by
    simpa using (Trace.single (Step.split pivotSplay)).context [] [incoming]
  have second : SplayTrace [old, right, incoming]
      [.split [] upper (inorder b)] [old, .empty, b, incoming] (rightWork + 1) := by
    simpa [inorder] using (Trace.single (Step.split rightSplay)).context [old] [incoming]
  have firstOrder : ([old, .empty, b, incoming] : List (RawTree α)).Perm [.empty, b, incoming, old] := by
    simpa using (List.perm_middle : ([.empty, b, incoming] ++ [old]).Perm (old :: [.empty, b, incoming])).symm
  have secondOrder : ([.empty, b, incoming, old] : List (RawTree α)).Perm [.empty, incoming, b, old] :=
    List.Perm.cons .empty (List.Perm.swap incoming b [old])
  have third : SplayTrace [.empty, incoming, b, old]
      [.join (inorder incoming) upper (inorder b)] [.empty, .node incoming upper b, old] 1 := by
    simpa using (Trace.single (Step.join incoming b upper)).context [.empty] [old]
  have fourth : SplayTrace [.empty, .node incoming upper b, old]
      [.join [] pivot (inorder (.node incoming upper b))] [.node .empty pivot (.node incoming upper b), old] 1 := by
    simpa [inorder] using (Trace.single (Step.join .empty (.node incoming upper b) pivot)).context [] [old]
  have total := first.append (second.append
    ((Trace.single (Step.reorder (firstOrder.trans secondOrder))).append (third.append fourth)))
  have rightKeys := rightSplay.inorder_eq
  simpa [noLowerWord, rightKeys, inorder, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using total

theorem noUpper_exact {whole left a old incoming : RawTree α}
    {lower pivot : α} {pivotWork leftWork : Nat}
    (pivotSplay : Auxiliary.Splay pivot whole (.node left pivot .empty) pivotWork)
    (leftSplay : Auxiliary.Splay lower left (.node a lower old) leftWork) :
    SplayTrace [whole, incoming] (noUpperWord (inorder a) (inorder old) (inorder incoming) lower pivot)
      [.node (.node a lower .empty) pivot incoming, old] (pivotWork + leftWork + 4) := by
  have first : SplayTrace [whole, incoming]
      [.split (inorder left) pivot []] [left, .empty, incoming] (pivotWork + 1) := by
    simpa [inorder] using (Trace.single (Step.split pivotSplay)).context [] [incoming]
  have second : SplayTrace [left, .empty, incoming]
      [.split (inorder a) lower (inorder old)] [a, old, .empty, incoming] (leftWork + 1) := by
    simpa using (Trace.single (Step.split leftSplay)).context [] [.empty, incoming]
  have order : ([a, old, .empty, incoming] : List (RawTree α)).Perm [a, .empty, incoming, old] := by
    apply List.Perm.cons a
    simpa using (List.perm_middle : ([.empty, incoming] ++ [old]).Perm (old :: [.empty, incoming])).symm
  have third : SplayTrace [a, .empty, incoming, old]
      [.join (inorder a) lower []] [.node a lower .empty, incoming, old] 1 := by
    simpa [inorder] using (Trace.single (Step.join a .empty lower)).context [] [incoming, old]
  have fourth : SplayTrace [.node a lower .empty, incoming, old]
      [.join (inorder (.node a lower .empty)) pivot (inorder incoming)]
      [.node (.node a lower .empty) pivot incoming, old] 1 := by
    simpa using (Trace.single (Step.join (.node a lower .empty) incoming pivot)).context [] [old]
  have total := first.append (second.append ((Trace.single (Step.reorder order)).append (third.append fourth)))
  have leftKeys := leftSplay.inorder_eq
  simpa [noUpperWord, leftKeys, inorder, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using total

theorem noGuards_exact {whole old incoming : RawTree α} {pivot : α} {work : Nat}
    (pivotSplay : Auxiliary.Splay pivot whole (.node old pivot .empty) work) :
    SplayTrace [whole, incoming] (noGuardsWord (inorder old) (inorder incoming) pivot)
      [.node .empty pivot incoming, old] (work + 2) := by
  have first : SplayTrace [whole, incoming]
      [.split (inorder old) pivot []] [old, .empty, incoming] (work + 1) := by
    simpa [inorder] using (Trace.single (Step.split pivotSplay)).context [] [incoming]
  have order : ([old, .empty, incoming] : List (RawTree α)).Perm [.empty, incoming, old] := by
    simpa using (List.perm_middle : ([.empty, incoming] ++ [old]).Perm (old :: [.empty, incoming])).symm
  have second : SplayTrace [.empty, incoming, old]
      [.join [] pivot (inorder incoming)] [.node .empty pivot incoming, old] 1 := by
    simpa [inorder] using (Trace.single (Step.join .empty incoming pivot)).context [] [old]
  simpa [noGuardsWord, Nat.add_assoc] using first.append ((Trace.single (Step.reorder order)).append second)

end MultiSplay.CommonForest
