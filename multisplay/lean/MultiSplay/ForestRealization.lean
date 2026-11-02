import MultiSplay.ForestDomains
import MultiSplay.SplayPointer
import Mathlib.Data.List.Basic

/-!
# Realizing a common domain word by physical splaying

`PointerSplay` retains both the standard splay transcript and its implementation
in the shared pointer model. `Event.CanSplay` says that a searched key is present
and that a split pivot occurs exactly at the specified cut. Joins impose no
additional execution requirement: they are the prescribed raw root insertion.

Every admissible domain trace can be replayed from any forest with those exact
ordered domains. The theorem constructs the actual surviving child trees, and
uses them in all subsequent operations; it never resets their shapes.
-/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder rootKey)
open ChaCha.MTR.Pointer (Frame)

variable {α : Type*}

def PointerSplay : Access α := fun key a b rotations =>
  Auxiliary.Splay key a b rotations ∧
  ∀ outer : List (Frame α),
    ChaCha.MTR.Pointer.Trace ⟨a, outer⟩ [key] ⟨b, outer⟩ (3 * rotations + 1)

abbrev PointerSplayTrace := @Trace α PointerSplay idle

theorem exists_pointer_access {tree : RawTree α} {key : α}
    (member : key ∈ inorder tree) : ∃ after rotations, PointerSplay key tree after rotations :=
  Auxiliary.exists_pointer_splay member

def Event.CanSplay : Event α → Prop
  | .search keys key => key ∈ keys
  | .split left pivot right => pivot ∉ left ∧ pivot ∉ right
  | .join _ _ _ => True

/-- The exact cut domains determine the children after exposing the pivot,
regardless of the original auxiliary shape. -/
theorem exists_pointer_split {tree : RawTree α} {left right : List α} {pivot : α}
    (keys : inorder tree = left ++ [pivot] ++ right)
    (unique : pivot ∉ left ∧ pivot ∉ right) :
    ∃ l r rotations, PointerSplay pivot tree (.node l pivot r) rotations ∧
      inorder l = left ∧ inorder r = right := by
  have member : pivot ∈ inorder tree := by simp [keys]
  obtain ⟨after, rotations, run, physical⟩ := exists_pointer_access member
  have root := run.root_after
  cases after with
  | empty => simp [rootKey] at root
  | node l key r =>
      simp only [rootKey, Option.some.injEq] at root
      subst key
      have same : left ++ pivot :: right = inorder l ++ pivot :: inorder r := by
        simpa [inorder, List.append_assoc] using keys.symm.trans run.inorder_eq
      have pieces := (List.append_cons_inj_of_notMem unique.1 unique.2).mp same
      exact ⟨l, r, rotations, ⟨run, physical⟩, pieces.1.symm, pieces.2.2.symm⟩

theorem Domains.Step.realize {a b : List (List α)} {word : List (Event α)}
    (step : Domains.Step a word b) (valid : ∀ event ∈ word, event.CanSplay)
    {initial : List (RawTree α)} (same : domains initial = a) :
    ∃ final work, PointerSplayTrace initial word final work ∧ domains final = b := by
  induction step generalizing initial with
  | search keys key =>
      obtain ⟨tree, rfl, domain⟩ := List.map_eq_singleton_iff.mp same
      have member := valid (.search keys key) (by simp)
      obtain ⟨after, work, run⟩ := exists_pointer_access (tree := tree) (key := key) (by rw [domain]; exact member)
      refine ⟨[after], work + 1, ?_, ?_⟩
      · simpa [domain] using (Trace.single (CommonForest.Step.search run))
      · simp only [domains, List.map_cons, List.map_nil, List.cons.injEq, and_true]
        exact run.1.inorder_eq.symm.trans domain
  | split left pivot right =>
      obtain ⟨tree, rfl, domain⟩ := List.map_eq_singleton_iff.mp same
      obtain ⟨l, r, work, run, leftKeys, rightKeys⟩ :=
        exists_pointer_split domain (valid (.split left pivot right) (by simp))
      refine ⟨[l, r], work + 1, ?_, ?_⟩
      · simpa [leftKeys, rightKeys] using (Trace.single (CommonForest.Step.split run))
      · simp [domains, leftKeys, rightKeys]
  | join left pivot right =>
      obtain ⟨l, rest, rfl, leftKeys, restKeys⟩ := List.map_eq_cons_iff.mp same
      obtain ⟨r, rfl, rightKeys⟩ := List.map_eq_singleton_iff.mp restKeys
      refine ⟨[.node l pivot r], 1, ?_, ?_⟩
      · simpa [leftKeys, rightKeys] using
          (Trace.single (CommonForest.Step.join (access := PointerSplay) (prepare := CommonForest.idle) l r pivot))
      · simp [domains, inorder, leftKeys, rightKeys]
  | idle keys => exact ⟨initial, 0, .nil _, same⟩
  | @context a b word step front back ih =>
      obtain ⟨initialFront, rest, rfl, frontKeys, restKeys⟩ :=
        List.map_eq_append_iff.mp (show initial.map inorder = front ++ (a ++ back) by
          simpa [domains, List.append_assoc] using same)
      obtain ⟨selected, initialBack, rfl, selectedKeys, backKeys⟩ :=
        List.map_eq_append_iff.mp restKeys
      obtain ⟨final, work, run, finalKeys⟩ := ih valid selectedKeys
      refine ⟨initialFront ++ final ++ initialBack, work, ?_, ?_⟩
      · simpa [List.append_assoc] using run.context initialFront initialBack
      · simp only [domains, List.map_append]
        rw [frontKeys, show final.map inorder = b from finalKeys, backKeys]
  | @reorder a b order =>
      have mapped : b.Perm (initial.map inorder) := by
        simpa only [← same, domains] using order.symm
      have lifted := Eq.mpr (congrFun (congrFun (List.eq_map_comp_perm inorder) b) initial) mapped
      obtain ⟨final, finalKeys, perm⟩ := lifted
      exact ⟨final, 0, Trace.single (CommonForest.Step.reorder perm.symm), finalKeys.symm⟩

/-- Realize the entire word chronologically. Future operations consume the
actual forest returned by the preceding operation. -/
theorem Domains.Trace.realize {a b : List (List α)} {word : List (Event α)}
    (trace : Domains.Trace a word b) (valid : ∀ event ∈ word, event.CanSplay)
    {initial : List (RawTree α)} (same : domains initial = a) :
    ∃ final work, PointerSplayTrace initial word final work ∧ domains final = b := by
  induction trace generalizing initial with
  | nil => exact ⟨initial, 0, .nil _, same⟩
  | cons step remaining ih =>
      obtain ⟨middle, firstWork, firstRun, middleKeys⟩ :=
        step.realize (fun event member => valid event (List.mem_append_left _ member)) same
      obtain ⟨final, restWork, restRun, finalKeys⟩ :=
        ih (fun event member => valid event (List.mem_append_right _ member)) middleKeys
      exact ⟨final, firstWork + restWork, firstRun.append restRun, finalKeys⟩

theorem Step.map_relations {access otherAccess : Access α} {prepare otherPrepare : Preparation α}
    (accessMap : ∀ {key a b work}, access key a b work → otherAccess key a b work)
    (prepareMap : ∀ {a b work}, prepare a b work → otherPrepare a b work)
    {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (step : Step access prepare a word b work) : Step otherAccess otherPrepare a word b work := by
  induction step with
  | search run => exact .search (accessMap run)
  | split run => exact .split (accessMap run)
  | join l r pivot => exact .join l r pivot
  | prepare run => exact .prepare (prepareMap run)
  | context step front back ih => exact ih.context front back
  | reorder order => exact .reorder order

theorem Trace.map_relations {access otherAccess : Access α} {prepare otherPrepare : Preparation α}
    (accessMap : ∀ {key a b work}, access key a b work → otherAccess key a b work)
    (prepareMap : ∀ {a b work}, prepare a b work → otherPrepare a b work)
    {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (trace : Trace access prepare a word b work) : Trace otherAccess otherPrepare a word b work := by
  induction trace with
  | nil => exact .nil _
  | cons step rest ih => exact .cons (step.map_relations accessMap prepareMap) ih

theorem PointerSplayTrace.toSplay {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (trace : PointerSplayTrace a word b work) : SplayTrace a word b work :=
  trace.map_relations (fun {_ _ _ _} run => run.1) (fun {_ _ _} run => run)

end MultiSplay.CommonForest
