import OrderedFamilyProcess
import OrderedBlockCuts

/-!
Concrete rank-cut operations are literal closed-family history edits.
This connects the spatial implementation, including unchanged blocks and
both fresh split descendants, to the ordered-history process.
-/

namespace GreedyMerge.HistoryProcess

open OrderedBlocks

theorem Edit.context {before after : List Frozen} (edit : Edit before after)
    (pre post : List Frozen) : Edit (pre ++ before ++ post) (pre ++ after ++ post) := by
  cases edit with
  | split left right focus cut leftId rightId =>
      simpa only [List.append_assoc, List.cons_append] using
        Edit.split (pre ++ left) (right ++ post) focus cut leftId rightId
  | erase left right focus key =>
      simpa only [List.append_assoc, List.cons_append] using
        Edit.erase (pre ++ left) (right ++ post) focus key
  | rebase left right focus base =>
      simpa only [List.append_assoc, List.cons_append] using
        Edit.rebase (pre ++ left) (right ++ post) focus base
  | perm permutation =>
      exact Edit.perm ((List.Perm.refl pre).append permutation |>.append (List.Perm.refl post))

theorem Run.context {before after : List Frozen} (run : Run before after)
    (pre post : List Frozen) : Run (pre ++ before ++ post) (pre ++ after ++ post) := by
  induction run with
  | nil _ => exact .nil _
  | cons step rest ih => exact .cons (step.context pre post) ih

theorem Run.trans {first second third : List Frozen}
    (left : Run first second) (right : Run second third) : Run first third := by
  induction left with
  | nil _ => exact right
  | cons step rest ih => exact .cons step (ih right)

theorem Run.refines {before after : List Frozen} (run : Run before after) (family : ℕ) :
    GreedyForest.Refines (FrozenHistory.familyView family after)
      (FrozenHistory.familyView family before) := by
  induction run with
  | nil blocks =>
      intro members present
      exact ⟨members, present, Finset.Subset.refl _⟩
  | cons step rest ih =>
      intro members present
      obtain ⟨middle, middleMember, middleSubset⟩ := ih members present
      obtain ⟨original, originalMember, originalSubset⟩ := step.refines family middle middleMember
      exact ⟨original, originalMember, middleSubset.trans originalSubset⟩

theorem cutBlock_history_run (side : Bool) (cut leftId rightId : ℕ) (block : Frozen) :
    Run [block] (cutBlock side cut leftId rightId block) := by
  classical
  by_cases crossing : Straddles cut block
  · let position := block.members.findIdx (fun entry => !cutPrefix side cut entry)
    have exactSplit : cutBlock side cut leftId rightId block =
        splitFresh leftId rightId block position := by
      simp only [cutBlock, if_pos crossing, splitFresh, splitLeft, splitRight,
        List.takeWhile_eq_take_findIdx_not, List.dropWhile_eq_drop_findIdx_not, position]
    rw [exactSplit]
    exact .cons (Edit.split [] [] block position leftId rightId) (.nil _)
  · simpa only [cutBlock, if_neg crossing] using Run.nil [block]

theorem cutList_history_run (side : Bool) (cut fresh : ℕ) (blocks : List Frozen) :
    Run blocks (cutList side cut fresh blocks) := by
  induction blocks generalizing fresh with
  | nil => exact .nil []
  | cons block rest ih =>
      have first := (cutBlock_history_run side cut fresh (fresh + 1) block).context [] rest
      have second := (ih (fresh + 2)).context (cutBlock side cut fresh (fresh + 1) block) []
      simp only [List.nil_append, List.singleton_append, List.append_nil] at first second
      have result := first.trans second
      simpa only [List.nil_append, List.singleton_append, List.append_nil, cutList] using result

/-- Arbitrary actual cut passes preserve the ordering of original entry
times in every inherited family, even when that orientation is reversed. -/
theorem cutList_history_valid (side : Bool) (cut fresh : ℕ) (blocks : List Frozen)
    (valid : Valid blocks) : Valid (cutList side cut fresh blocks) :=
  (cutList_history_run side cut fresh blocks).valid valid

theorem cutList_family_ordered (side : Bool) (cut fresh family : ℕ) (blocks : List Frozen)
    (valid : Valid blocks) :
    GreedyForest.OrderedFamily (FrozenHistory.familyView family (cutList side cut fresh blocks)) :=
  family_ordered family _ (cutList_history_valid side cut fresh blocks valid)

end GreedyMerge.HistoryProcess

#print axioms GreedyMerge.HistoryProcess.cutList_history_run
#print axioms GreedyMerge.HistoryProcess.cutList_family_ordered
