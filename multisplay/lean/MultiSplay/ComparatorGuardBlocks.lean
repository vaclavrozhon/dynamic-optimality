import MultiSplay.ComparatorGuardProjection
import MultiSplay.ComparatorCheckpoints
import MultiSplay.ClassicalSwitchWord

/-! # Constant-cost guard checkpoints on opaque projected blocks

All blocks below are the literal record-free pieces of the maintained
projection. Reassociation changes only their joins. In particular it does
not search within, rebuild, or charge the size of a detached path.
-/

namespace MultiSplay.ComparatorGuard

open ChaCha Paper20261030 ColoredStorage SourcePointer
open CommonForest

variable {α : Type*}

def BlockRearranges : Block α → Block α → Nat → Prop
  | none,none,_ => True
  | some left,some right,budget => SourcePointer.Rearranges left right budget
  | _,_,_ => False

theorem block_refl (tree : Block α) (budget : Nat) : BlockRearranges tree tree budget := by
  cases tree
  · trivial
  · exact rearranges_refl _ _

theorem BlockRearranges.mono {before after : Block α} {m n : Nat}
    (run : BlockRearranges before after m) (bound : m ≤ n) : BlockRearranges before after n := by
  cases before <;> cases after
  all_goals first | trivial | exact False.elim run | exact Rearranges.mono run bound

theorem BlockRearranges.trans {a b c : Block α} {m n : Nat}
    (first : BlockRearranges a b m) (second : BlockRearranges b c n) :
    BlockRearranges a c (m+n) := by
  cases a <;> cases b <;> cases c
  all_goals first | trivial | exact False.elim first | exact False.elim second |
    exact Rearranges.trans first second

theorem BlockRearranges.symm {before after : Block α} {budget : Nat}
    (run : BlockRearranges before after budget) : BlockRearranges after before budget := by
  cases before <;> cases after
  all_goals first | trivial | exact False.elim run | exact Rearranges.symm run

theorem BlockRearranges.left {before after right : Block α} {budget : Nat}
    (run : BlockRearranges before after budget) :
    BlockRearranges (join before right) (join after right) (budget+2) := by
  cases before <;> cases after <;> cases right
  all_goals first | exact block_refl _ _ | exact False.elim run |
    exact Rearranges.mono run (by omega) | exact Rearranges.left run

theorem BlockRearranges.right {left before after : Block α} {budget : Nat}
    (run : BlockRearranges before after budget) :
    BlockRearranges (join left before) (join left after) (budget+2) := by
  cases before <;> cases after <;> cases left
  all_goals first | exact block_refl _ _ | exact False.elim run |
    exact Rearranges.mono run (by omega) | exact Rearranges.right run

theorem block_associate (a b c : Block α) :
    BlockRearranges (join (join a b) c) (join a (join b c)) 1 := by
  cases a <;> cases b <;> cases c
  all_goals first | exact block_refl _ _ |
    exact fun ancestors => ⟨[],1,.step (.rotateRight _ _ _ _ _ ancestors) (.nil _),le_rfl⟩

@[simp] theorem componentBlock_join (left right : Block α) (terminal : α) :
    some (componentBlock left right terminal) =
      join (join left (some (.leaf terminal ()))) right := by
  cases left <;> cases right <;> rfl

def withLeft (front : Block α) (tree : Plain α) : Plain α :=
  match front with
  | none => tree
  | some front => .fork () front tree

def withRight (tree : Plain α) (suffix : Block α) : Plain α :=
  match suffix with
  | none => tree
  | some suffix => .fork () tree suffix

@[simp] theorem some_withLeft (front : Block α) (tree : Plain α) :
    some (withLeft front tree) = join front (some tree) := by cases front <;> rfl

@[simp] theorem some_withRight (tree : Plain α) (suffix : Block α) :
    some (withRight tree suffix) = join (some tree) suffix := by cases suffix <;> rfl

/-- The exposed old-left source before its two color wings are regrouped. -/
def leftSource (prefixLeft prefixRight oldLeft oldRight : Block α)
    (oldTerminal upper : α) : Plain α :=
  componentBlock (join prefixLeft oldLeft)
    (join (join oldRight (some (.leaf upper ()))) prefixRight) oldTerminal

/-- The exposed new-right source after its two color wings are regrouped. -/
def rightSource (prefixLeft prefixRight incomingLeft incomingRight : Block α)
    (incomingTerminal pivot : α) : Plain α :=
  componentBlock (join prefixLeft (join (some (.leaf pivot ())) incomingLeft))
    (join incomingRight prefixRight) incomingTerminal

def checkpointBefore (front suffix : Block α) (old : Plain α) (upper : α) : Plain α :=
  .fork () (withLeft front old) (withRight (.leaf upper ()) suffix)

def checkpointAfter (front suffix : Block α) (incoming : Plain α) (pivot : α) : Plain α :=
  .fork () (withLeft front (.leaf pivot ())) (withRight incoming suffix)

/-- Four root reassociations expose both guards simultaneously. -/
theorem leftSource_prepare (prefixLeft prefixRight oldLeft oldRight : Block α)
    (oldTerminal upper : α) :
    SourcePointer.Rearranges (leftSource prefixLeft prefixRight oldLeft oldRight oldTerminal upper)
      (checkpointBefore prefixLeft prefixRight (componentBlock oldLeft oldRight oldTerminal) upper) 10 := by
  let terminal : Block α := some (.leaf oldTerminal ())
  let upperLeaf : Block α := some (.leaf upper ())
  have first := (block_associate prefixLeft oldLeft terminal).left
    (right := join (join oldRight upperLeaf) prefixRight)
  have second := (block_associate oldRight upperLeaf prefixRight).right
    (left := join prefixLeft (join oldLeft terminal))
  have third := (block_associate (join prefixLeft (join oldLeft terminal)) oldRight
    (join upperLeaf prefixRight)).symm
  have fourth := (block_associate prefixLeft (join oldLeft terminal) oldRight).left
    (right := join upperLeaf prefixRight)
  have run := ((first.trans second).trans third).trans fourth
  have source : some (leftSource prefixLeft prefixRight oldLeft oldRight oldTerminal upper) =
      join (join (join prefixLeft oldLeft) terminal) (join (join oldRight upperLeaf) prefixRight) :=
    componentBlock_join _ _ _
  have target : some (checkpointBefore prefixLeft prefixRight (componentBlock oldLeft oldRight oldTerminal) upper) =
      join (join prefixLeft (join (join oldLeft terminal) oldRight)) (join upperLeaf prefixRight) := by
    cases prefixLeft <;> cases prefixRight <;> cases oldLeft <;> cases oldRight <;> rfl
  rw [← source,← target] at run
  exact run

/-- The new source uses the same front blocks and literal incoming tail. -/
theorem rightSource_prepare (prefixLeft prefixRight incomingLeft incomingRight : Block α)
    (incomingTerminal pivot : α) :
    SourcePointer.Rearranges (rightSource prefixLeft prefixRight incomingLeft incomingRight incomingTerminal pivot)
      (checkpointAfter prefixLeft prefixRight (componentBlock incomingLeft incomingRight incomingTerminal) pivot) 12 := by
  let terminal : Block α := some (.leaf incomingTerminal ())
  let pivotLeaf : Block α := some (.leaf pivot ())
  have first := ((block_associate prefixLeft pivotLeaf incomingLeft).symm.left
    (right := terminal)).left (right := join incomingRight prefixRight)
  have second := (block_associate (join prefixLeft pivotLeaf) incomingLeft terminal).left
    (right := join incomingRight prefixRight)
  have third := block_associate (join prefixLeft pivotLeaf) (join incomingLeft terminal)
    (join incomingRight prefixRight)
  have fourth := (block_associate (join incomingLeft terminal) incomingRight prefixRight).symm.right
    (left := join prefixLeft pivotLeaf)
  have run := ((first.trans second).trans third).trans fourth
  have source : some (rightSource prefixLeft prefixRight incomingLeft incomingRight incomingTerminal pivot) =
      join (join (join prefixLeft (join pivotLeaf incomingLeft)) terminal) (join incomingRight prefixRight) :=
    componentBlock_join _ _ _
  have target : some (checkpointAfter prefixLeft prefixRight (componentBlock incomingLeft incomingRight incomingTerminal) pivot) =
      join (join prefixLeft pivotLeaf) (join (join (join incomingLeft terminal) incomingRight) prefixRight) := by
    cases prefixLeft <;> cases prefixRight <;> cases incomingLeft <;> cases incomingRight <;> rfl
  rw [← source,← target] at run
  exact run

def lowerBoundary : Block α → ClassicalSwitch.Boundary α
  | none => .absent
  | some front => .guard (GapBST.gaps front).inorder (GapBST.lastKey front)

def upperBoundary (upper : α) : Block α → ClassicalSwitch.Boundary α
  | none => .absent
  | some suffix => .guard (GapBST.gaps suffix).inorder upper

/-- The exact classical word, including absent guards and empty tails. -/
theorem block_checkpoints (front suffix : Block α) (old incoming : Plain α)
    (pivot upper : α) (oldLast : GapBST.lastKey old = pivot)
    (incomingLast : GapBST.lastKey incoming = upper) :
    Program [GapBST.gaps (checkpointBefore front suffix old upper),GapBST.gaps incoming]
      (ClassicalSwitch.leftWord (lowerBoundary front) (upperBoundary upper suffix)
        (GapBST.gaps old).inorder (GapBST.gaps incoming).inorder pivot)
      [GapBST.gaps (checkpointAfter front suffix incoming pivot),GapBST.gaps old]
      (2+2*(lowerBoundary front).count+2*(upperBoundary upper suffix).count) := by
  cases front with
  | none =>
      cases suffix with
      | none => simpa [checkpointBefore,checkpointAfter,withLeft,withRight,GapBST.gaps,
          GapBST.lastKey,oldLast,incomingLast,lowerBoundary,upperBoundary,
          ClassicalSwitch.Boundary.count,ClassicalSwitch.leftWord] using
            noGuards_checkpoints (GapBST.gaps old) (GapBST.gaps incoming) pivot
      | some suffix => simpa [checkpointBefore,checkpointAfter,withLeft,withRight,GapBST.gaps,
          GapBST.lastKey,oldLast,incomingLast,lowerBoundary,upperBoundary,
          ClassicalSwitch.Boundary.count,ClassicalSwitch.leftWord] using
            noLower_checkpoints (GapBST.gaps old) (GapBST.gaps incoming) (GapBST.gaps suffix) pivot upper
  | some front =>
      cases suffix with
      | none => simpa [checkpointBefore,checkpointAfter,withLeft,withRight,GapBST.gaps,
          GapBST.lastKey,oldLast,incomingLast,lowerBoundary,upperBoundary,
          ClassicalSwitch.Boundary.count,ClassicalSwitch.leftWord] using
            (noUpper_checkpoints (GapBST.gaps front) (GapBST.gaps old) (GapBST.gaps incoming)
              (GapBST.lastKey front) pivot)
      | some suffix => simpa [checkpointBefore,checkpointAfter,withLeft,withRight,GapBST.gaps,
          GapBST.lastKey,oldLast,incomingLast,lowerBoundary,upperBoundary,
          ClassicalSwitch.Boundary.count,ClassicalSwitch.leftWord] using
            (leftToRight_checkpoints (GapBST.gaps front) (GapBST.gaps old) (GapBST.gaps incoming)
              (GapBST.gaps suffix) (GapBST.lastKey front) pivot upper)

/-- Uniform constant preparation, exact checkpoints, and reconstruction of
both output representations. No operation enters an opaque block. -/
theorem left_block_service (prefixLeft prefixRight oldLeft oldRight incomingLeft incomingRight : Block α)
    (oldTerminal incomingTerminal pivot upper : α)
    (oldLast : GapBST.lastKey (componentBlock oldLeft oldRight oldTerminal) = pivot)
    (incomingLast : GapBST.lastKey (componentBlock incomingLeft incomingRight incomingTerminal) = upper) :
    ∃ work ≤ 294,
      Program [GapBST.gaps (leftSource prefixLeft prefixRight oldLeft oldRight oldTerminal upper),
          GapBST.gaps (componentBlock incomingLeft incomingRight incomingTerminal)]
        (ClassicalSwitch.leftWord (lowerBoundary prefixLeft) (upperBoundary upper prefixRight)
          (GapBST.gaps (componentBlock oldLeft oldRight oldTerminal)).inorder
          (GapBST.gaps (componentBlock incomingLeft incomingRight incomingTerminal)).inorder pivot)
        [GapBST.gaps (rightSource prefixLeft prefixRight incomingLeft incomingRight incomingTerminal pivot),
          GapBST.gaps (componentBlock oldLeft oldRight oldTerminal)] work := by
  obtain ⟨first,firstBound,prepare⟩ := ComparatorGap.rearranges_program
    (leftSource_prepare prefixLeft prefixRight oldLeft oldRight oldTerminal upper)
  obtain ⟨last,lastBound,restore⟩ := ComparatorGap.rearranges_program
    (rightSource_prepare prefixLeft prefixRight incomingLeft incomingRight incomingTerminal pivot).symm
  have middle := block_checkpoints prefixLeft prefixRight
    (componentBlock oldLeft oldRight oldTerminal) (componentBlock incomingLeft incomingRight incomingTerminal)
    pivot upper oldLast incomingLast
  have lowerCount := (lowerBoundary prefixLeft).count_le_one
  have upperCount := (upperBoundary upper prefixRight).count_le_one
  refine ⟨first+(2+2*(lowerBoundary prefixLeft).count+2*(upperBoundary upper prefixRight).count)+last,
    by omega,?_⟩
  simpa using ((prepare.context [] [GapBST.gaps (componentBlock incomingLeft incomingRight incomingTerminal)]).append
    middle).append (restore.context [] [GapBST.gaps (componentBlock oldLeft oldRight oldTerminal)])

end MultiSplay.ComparatorGuard
