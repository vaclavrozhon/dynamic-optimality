import DynamicOptimality.SingleFinger.SourceCounted

/-! Actual bounded-depth search with one source pointer.

The controller reads records and traverses both children to a fixed depth.
Its registers contain a bounded stack of adjacent moves and remaining depths,
never a source tree or an address supplied by the representation invariant.
The scanner's reads are physical metadata observations, not application
access events. A caller must separately identify the requested source leaf.
-/

namespace DynamicOptimality.SingleFinger.BoundedScan

open TangoSquared.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ : Type*}

inductive Task where
  | inspect (depth : Nat)
  | move (action : DynamicOptimality.LocalProgram.Move)

inductive State (ρ : Type*) where
  | running (tasks : List Task)
  | found (record : ρ) (leaf : Bool)

def children (depth : Nat) (rest : List Task) : List Task :=
  [.move .left,.inspect depth,.move .up,.move .right,.inspect depth,.move .up]++rest

def code (test : ρ → Bool) : Program (State ρ) ρ
  | .found _ _ => .halt
  | .running [] => .halt
  | .running (.move action::rest) => .nav action (.running rest)
  | .running (.inspect depth::rest) => .read fun record leaf =>
    if test record then .found record leaf
    else .running (match depth with
      | 0 => rest
      | depth+1 => if leaf then rest else children depth rest)

def contains (test : ρ → Bool) : Nat → Source α ρ → Bool
  | 0, tree => test tree.rootRecord
  | _+1, .leaf _ record => test record
  | depth+1, .fork record left right =>
      test record || contains test depth left || contains test depth right

def budget : Nat → Nat
  | 0 => 1
  | depth+1 => 2*budget depth+5

theorem budget_positive (depth : Nat) : 1 ≤ budget depth := by
  cases depth <;> simp [budget]

/-- A successful scan returns the reached record and its actual leaf bit;
failure restores the starting pointer and continues with the supplied tasks. -/
def Result (test : ρ → Bool) (depth : Nat) (tree : Source α ρ)
    (outside : List (Frame α ρ)) (rest : List Task) (state : State ρ) (after : Cursor α ρ) : Prop :=
  (contains test depth tree = false ∧ state = .running rest ∧ after = ⟨tree,outside⟩) ∨
  (contains test depth tree = true ∧
    state = .found after.focus.rootRecord (isLeaf after.focus) ∧
    test after.focus.rootRecord = true ∧
    after.tree = SourcePointer.plug tree outside ∧
    after.ancestors.length ≤ outside.length+depth)

theorem execute (test : ρ → Bool) (depth : Nat) (tree : Source α ρ)
    (outside : List (Frame α ρ)) (rest : List Task) :
    ∃ (state : State ρ) (after : Cursor α ρ) (reads : List ρ) (cost : Nat),
      Steps (code test) (.running (.inspect depth::rest)) ⟨tree,outside⟩ state after reads cost ∧
      cost ≤ budget depth ∧ Result test depth tree outside rest state after := by
  by_cases hit : test tree.rootRecord = true
  · refine ⟨.found tree.rootRecord (isLeaf tree),⟨tree,outside⟩,[tree.rootRecord],1,?_,
      budget_positive depth,Or.inr ⟨?_,rfl,hit,rfl,by simp⟩⟩
    · simpa only [code,hit,ite_true,Option.toList_some] using
        (Step.read (program := code test) (state := .running (.inspect depth::rest))
          (cursor := ⟨tree,outside⟩) rfl).prefix
    · cases depth <;> cases tree <;> simp_all [contains,Source.rootRecord]
  · have miss : test tree.rootRecord = false := Bool.eq_false_iff.mpr hit
    cases depth with
    | zero =>
      refine ⟨.running rest,⟨tree,outside⟩,[tree.rootRecord],1,?_,le_rfl,
        Or.inl ⟨miss,rfl,rfl⟩⟩
      simpa only [code,miss,Bool.false_eq_true,ite_false,Option.toList_some] using
        (Step.read (program := code test) (state := .running (.inspect 0::rest))
          (cursor := ⟨tree,outside⟩) rfl).prefix
    | succ depth =>
      cases tree with
      | leaf key record =>
        refine ⟨.running rest,⟨.leaf key record,outside⟩,[record],1,?_,
          budget_positive _,Or.inl ⟨miss,rfl,rfl⟩⟩
        have recordMiss : test record = false := miss
        simpa only [code,Source.rootRecord,isLeaf,recordMiss,Bool.false_eq_true,ite_false,ite_true,
          Option.toList_some] using
          (Step.read (program := code test) (state := .running (.inspect (depth+1)::rest))
            (cursor := ⟨.leaf key record,outside⟩) rfl).prefix
      | fork record left right =>
        have recordMiss : test record = false := miss
        let leftRest := [.move .up,.move .right,.inspect depth,.move .up]++rest
        let rightRest := .move .up::rest
        obtain ⟨leftState,leftCursor,leftReads,leftCost,leftRun,leftBound,leftResult⟩ :=
          execute test depth left (.left record right::outside) leftRest
        have readStep : Step (code test) (.running (.inspect (depth+1)::rest))
            ⟨.fork record left right,outside⟩ (.running (children depth rest))
            ⟨.fork record left right,outside⟩ (some record) := by
          simpa only [code,Source.rootRecord,isLeaf,recordMiss,Bool.false_eq_true,ite_false] using
            (Step.read (program := code test) (state := .running (.inspect (depth+1)::rest))
              (cursor := ⟨.fork record left right,outside⟩) rfl)
        have leftDown : Step (code test) (.running (children depth rest))
            ⟨.fork record left right,outside⟩ (.running (.inspect depth::leftRest))
            ⟨left,.left record right::outside⟩ none := .nav rfl rfl
        rcases leftResult with ⟨leftMiss,leftStateEq,leftCursorEq⟩ | leftFound
        · subst leftState
          subst leftCursor
          obtain ⟨rightState,rightCursor,rightReads,rightCost,rightRun,rightBound,rightResult⟩ :=
            execute test depth right (.right left record::outside) rightRest
          have leftUp : Step (code test) (.running leftRest)
              ⟨left,.left record right::outside⟩
              (.running (.move .right::.inspect depth::.move .up::rest))
              ⟨.fork record left right,outside⟩ none := .nav rfl rfl
          have rightDown : Step (code test)
              (.running (.move .right::.inspect depth::.move .up::rest))
              ⟨.fork record left right,outside⟩ (.running (.inspect depth::rightRest))
              ⟨right,.right left record::outside⟩ none := .nav rfl rfl
          have first := (readStep.prefix.append leftDown.prefix).append
            (leftRun.append (leftUp.prefix.append rightDown.prefix))
          rcases rightResult with ⟨rightMiss,rightStateEq,rightCursorEq⟩ | rightFound
          · subst rightState
            subst rightCursor
            have rightUp : Step (code test) (.running rightRest)
                ⟨right,.right left record::outside⟩ (.running rest)
                ⟨.fork record left right,outside⟩ none := .nav rfl rfl
            refine ⟨.running rest,⟨.fork record left right,outside⟩,_,_,
              first.append (rightRun.append rightUp.prefix),?_,Or.inl ⟨?_,rfl,rfl⟩⟩
            · simp only [budget]
              omega
            · simp only [contains,show test record = false from miss,leftMiss,rightMiss]
              rfl
          · rcases rightFound with ⟨containsRight,foundRight,testRight,treeRight,depthRight⟩
            refine ⟨rightState,rightCursor,_,_,first.append rightRun,?_,
              Or.inr ⟨?_,foundRight,testRight,treeRight,?_⟩⟩
            · simp only [budget]
              omega
            · simp only [contains,containsRight,Bool.or_true]
            · simp only [List.length_cons] at depthRight
              omega
        · rcases leftFound with ⟨containsLeft,foundLeft,testLeft,treeLeft,depthLeft⟩
          refine ⟨leftState,leftCursor,_,_,
            readStep.prefix.append (leftDown.prefix.append leftRun),?_,
            Or.inr ⟨?_,foundLeft,testLeft,treeLeft,?_⟩⟩
          · simp only [budget]
            omega
          · simp only [contains,containsLeft,Bool.or_true,Bool.true_or]
          · simp only [List.length_cons] at depthLeft
            omega
termination_by depth

end DynamicOptimality.SingleFinger.BoundedScan
