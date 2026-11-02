import ChaCha.Paper20261030.BSTHistory
import ChaCha.Paper20261030.AccessWords

/-!
# The robust rectangle lower bound for actual BST executions

The history invariant constructs an arborally satisfied superset from
each actual rooted-hull execution. Its initial row at time -1 is removed
before counting; the remaining point count is at most the actual cost.
The existing pointer-to-hull theorem then gives the same lower bound for
ordinary BST pointer executions, including repeated requests.
-/

namespace ChaCha.Paper20261030.BSTHistory

open Rectangles MTR.Tree

theorem hull_execution_history {before after : MTR.Tree Int} {requests : List Int} {cost : Nat}
    (execution : MTR.AccessExecution before requests after cost) (ordered : before.Ordered)
    {history memory time} (valid : Valid before history memory time) :
    ∃ Y : Finset Point, history ⊆ Y ∧ (∀ point ∈ pointWord time requests, point ∈ Y) ∧
      ArboralDilation.Satisfied (Y : Set Point) ∧ Y.card ≤ history.card+cost := by
  induction execution generalizing history memory time with
  | nil => exact ⟨history,Finset.Subset.refl _,by simp [pointWord],valid.satisfied,by omega⟩
  | cons access rest ih =>
    have next := valid.step access ordered
    obtain ⟨Y,includes,requested,satisfied,bound⟩ := ih (access.ordered_after ordered) next
    have stepBound := augment_card history access.source.inorder time
    rw [length_inorder] at stepBound
    refine ⟨Y,fun point member => includes (old_mem member),?_,satisfied,?_⟩
    · intro point member
      obtain same | later := List.mem_cons.mp member
      · subst point
        exact includes (new_mem access.requested)
      · exact requested point later
    · change Y.card ≤ history.card+(access.source.size+_) 
      omega

theorem satisfied_nonnegative {Y : Finset Point} (satisfied : ArboralDilation.Satisfied (Y : Set Point)) :
    ArboralDilation.Satisfied (Y.filter (fun point => 0 ≤ point.2) : Set Point) := by
  intro a t b u aMember bMember ordered different
  obtain ⟨aIn,aTime⟩ := Finset.mem_filter.mp aMember
  obtain ⟨bIn,bTime⟩ := Finset.mem_filter.mp bMember
  obtain ⟨point,member,box,notA,notB⟩ := satisfied a t b u aIn bIn ordered different
  refine ⟨point,Finset.mem_filter.mpr ⟨member,?_⟩,box,notA,notB⟩
  exact (le_min aTime bTime).trans box.2.2.1

theorem hull_execution_satisfied {before after : MTR.Tree Int} {requests : List Int} {cost : Nat}
    (execution : MTR.AccessExecution before requests after cost) (ordered : before.Ordered) :
    ∃ Y : Finset Point, accessPoints requests ⊆ Y ∧ ArboralDilation.Satisfied (Y : Set Point) ∧ Y.card ≤ cost := by
  obtain ⟨full,includes,requested,satisfied,bound⟩ :=
    hull_execution_history execution ordered (initial_valid before)
  let Y := full.filter (fun point => 0 ≤ point.2)
  have disjoint : Disjoint (initialPoints before) Y := by
    apply Finset.disjoint_left.mpr
    intro point initial nonnegative
    obtain ⟨key,_,equal⟩ := Finset.mem_image.mp initial
    have timeEq := congrArg Prod.snd equal
    have timeBound := (Finset.mem_filter.mp nonnegative).2
    dsimp only at timeEq
    omega
  have contained : initialPoints before ∪ Y ⊆ full := Finset.union_subset includes (Finset.filter_subset _ _)
  have sumBound := Finset.card_le_card contained
  rw [Finset.card_union_of_disjoint disjoint] at sumBound
  refine ⟨Y,?_,satisfied_nonnegative satisfied,by omega⟩
  intro point member
  rw [← pointWord_toFinset] at member
  have inWord := List.mem_toFinset.mp member
  exact Finset.mem_filter.mpr ⟨requested point inWord,pointWord_time inWord⟩

theorem pointer_execution_satisfied {before after : MTR.Tree Int} {requests : List Int} {cost : Nat}
    (execution : MTR.Pointer.Execution before requests after cost) (ordered : before.Ordered) :
    ∃ Y : Finset Point, accessPoints requests ⊆ Y ∧ ArboralDilation.Satisfied (Y : Set Point) ∧ Y.card ≤ cost := by
  obtain ⟨hullCost,hullBound,hull⟩ := execution.toAccessExecution
  obtain ⟨Y,included,satisfied,bound⟩ := hull_execution_satisfied hull ordered
  exact ⟨Y,included,satisfied,bound.trans hullBound⟩

end ChaCha.Paper20261030.BSTHistory

namespace ChaCha.Paper20261030.Rectangles

theorem robustBound_le_pointer_cost {before after : MTR.Tree Int} {requests : List Int} {cost : Nat}
    (execution : MTR.Pointer.Execution before requests after cost) (ordered : before.Ordered) :
    robustBound (accessPoints requests) ≤ 2*cost := by
  obtain ⟨Y,included,satisfied,bound⟩ := BSTHistory.pointer_execution_satisfied execution ordered
  exact (robustBound_le_satisfied included satisfied).trans (Nat.mul_le_mul_left 2 bound)

end ChaCha.Paper20261030.Rectangles
