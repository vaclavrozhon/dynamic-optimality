import DynamicOptimality.Funnel.WarmMTR
import DynamicOptimality.Funnel.WarmVisibility
import DynamicOptimality.Funnel.ApproxMonotonicity.Prefix

/-! # Two search paths and the two interval restrictions

The targets need not already be in the tree. In that case the proper search
path ends at an empty child, and the later crossing analysis appends the same
terminal marker as for a present target. This permits the argument to start
from the empty warm Cartesian tree.
-/

namespace DynamicOptimality.Funnel.ApproxMonotonicity

open ChaCha.MTR ChaCha.MTR.Tree Warm

variable {α : Type*} [LinearOrder α]

def sidePath (x : α) (tree : Tree α) : List Bool :=
  (ancestors x tree).map (fun a => decide (a < x))

@[simp] theorem sidePath_empty (x : α) : sidePath x (.empty : Tree α) = [] := rfl

@[simp] theorem sidePath_root (l r : Tree α) (x : α) :
    sidePath x (.node l x r) = [] := by simp [sidePath,ancestors]

theorem sidePath_left (l r : Tree α) (a x : α) (less : x < a) :
    sidePath x (.node l a r) = false :: sidePath x l := by
  simp [sidePath,ancestors,less,not_lt_of_gt less]

theorem sidePath_right (l r : Tree α) (a x : α) (less : a < x) :
    sidePath x (.node l a r) = true :: sidePath x r := by
  simp [sidePath,ancestors,less,not_lt_of_gt less]

/-- The four ways in which two searches can leave their common prefix.
The last two lists are the paths after restricting above the smaller target
and below the larger target, respectively. -/
inductive SplitPaths : List Bool → List Bool → List Bool → List Bool → Prop where
  | absent (p : List Bool) :
      SplitPaths p p (p.filter (! ·)) (p.filter id)
  | lower (p xs : List Bool) :
      SplitPaths (p ++ true :: xs) p (p.filter (! ·) ++ xs) (p.filter id)
  | upper (p ys : List Bool) :
      SplitPaths p (p ++ false :: ys) (p.filter (! ·)) (p.filter id ++ ys)
  | fork (p xs ys : List Bool) :
      SplitPaths (p ++ true :: xs) (p ++ false :: ys)
        (p.filter (! ·) ++ true :: xs) (p.filter id ++ false :: ys)

private theorem SplitPaths.prepend_true {a b c d : List Bool} (h : SplitPaths a b c d) :
    SplitPaths (true :: a) (true :: b) c (true :: d) := by
  induction h with
  | absent p => simpa using SplitPaths.absent (true :: p)
  | lower p xs => simpa using SplitPaths.lower (true :: p) xs
  | upper p ys => simpa using SplitPaths.upper (true :: p) ys
  | fork p xs ys => simpa using SplitPaths.fork (true :: p) xs ys

private theorem SplitPaths.prepend_false {a b c d : List Bool} (h : SplitPaths a b c d) :
    SplitPaths (false :: a) (false :: b) (false :: c) d := by
  induction h with
  | absent p => simpa using SplitPaths.absent (false :: p)
  | lower p xs => simpa using SplitPaths.lower (false :: p) xs
  | upper p ys => simpa using SplitPaths.upper (false :: p) ys
  | fork p xs ys => simpa using SplitPaths.fork (false :: p) xs ys

/-- Exact simultaneous decomposition of the two original and restricted
search paths. It covers present keys, missing keys, and the empty tree. -/
theorem splitPaths (tree : Tree α) (ordered : Ordered tree) (x y : α) (yx : y < x) :
    SplitPaths (sidePath x tree) (sidePath y tree)
      (sidePath x (above y tree)) (sidePath y (below x tree)) := by
  induction tree with
  | empty => simpa [above,below] using SplitPaths.absent []
  | node l a r ihl ihr =>
    obtain ⟨ol,orr,left,right⟩ := ordered_parts ordered
    rcases lt_trichotomy a y with ay | rfl | ya
    · have ax := ay.trans yx
      have recurse := (ihr orr).prepend_true
      simpa [sidePath_right l r a x ax,sidePath_right l r a y ay,above,below,
        not_lt_of_gt ay,ax,sidePath_right _ _ a y ay] using recurse
    · have fixed := above_eq_self a r right
      simpa [sidePath_right l r a x yx,above,below,yx,fixed] using
        SplitPaths.lower [] (sidePath x r)
    · rcases lt_trichotomy a x with ax | rfl | xa
      · have fixedRight := above_eq_self y r (fun z hz => ya.trans (right z hz))
        have fixedLeft := below_eq_self x l (fun z hz => (left z hz).trans ax)
        simpa [sidePath_right l r a x ax,sidePath_left l r a y ya,
          above,below,ya,ax,fixedLeft,fixedRight,
          sidePath_right _ _ a x ax,sidePath_left _ _ a y ya] using
          SplitPaths.fork [] (sidePath x r) (sidePath y l)
      · have fixed := below_eq_self a l left
        simpa [sidePath_left l r a y yx,above,below,yx,fixed] using
          SplitPaths.upper [] (sidePath y l)
      · have ya' := yx.trans xa
        have recurse := (ihl ol).prepend_false
        simpa [sidePath_left l r a x xa,sidePath_left l r a y ya',above,below,
          ya',not_lt_of_gt xa,sidePath_left _ _ a x xa] using recurse

end DynamicOptimality.Funnel.ApproxMonotonicity
