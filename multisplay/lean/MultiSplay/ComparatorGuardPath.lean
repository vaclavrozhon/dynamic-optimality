import TangoSquared.PointerModel
import DynamicOptimality.Basic

/-!
# Original-key neighbors of an external gap

External gaps are numbered in inorder, starting with zero. A route records
the actual root-to-gap path. Both neighboring original keys lie on that
path, including boundary gaps and empty trees. Its marked hull retains all
unvisited subtrees literally as opaque holes.
-/

namespace MultiSplay.ComparatorGuard

open DynamicOptimality (RawTree)
open TangoSquared.MTR
open Pointer (MarkedTree)

variable {α : Type*}

inductive GapRoute : RawTree α → Nat → List α → Prop
  | empty : GapRoute .empty 0 []
  | left {left right : RawTree α} {root : α} {index : Nat} {keys : List α}
      (child : GapRoute left index keys) : GapRoute (.node left root right) index (root::keys)
  | right {left right : RawTree α} {root : α} {index : Nat} {keys : List α}
      (child : GapRoute right index keys) :
      GapRoute (.node left root right) (left.size + 1 + index) (root::keys)

 theorem GapRoute.bound {tree : RawTree α} {index : Nat} {keys : List α}
    (route : GapRoute tree index keys) : index ≤ tree.size := by
  induction route <;> simp only [Tree.size] at * <;> omega

 theorem gapRoute_exists (tree : RawTree α) (index : Nat) (bound : index ≤ tree.size) :
    ∃ keys, GapRoute tree index keys := by
  induction tree generalizing index with
  | empty => have zero : index = 0 := by simpa only [Tree.size, Nat.le_zero] using bound
             subst index
             exact ⟨[],.empty⟩
  | node left root right ihLeft ihRight =>
      by_cases inLeft : index ≤ left.size
      · obtain ⟨keys,route⟩ := ihLeft index inLeft
        exact ⟨root::keys,.left route⟩
      · have restBound : index - (left.size+1) ≤ right.size := by
          simp only [Tree.size] at bound
          omega
        obtain ⟨keys,route⟩ := ihRight (index-(left.size+1)) restBound
        refine ⟨root::keys,?_⟩
        have location : index = left.size+1+(index-(left.size+1)) := by omega
        rw [location]
        exact .right route

/-- The inorder key immediately to the right of a gap is an actual ancestor
on the gap's search path. A last gap has no such key. -/
theorem GapRoute.upper {tree : RawTree α} {index : Nat} {keys : List α} (route : GapRoute tree index keys)
    {key : α} (neighbor : tree.inorder[index]? = some key) : key ∈ keys := by
  induction route with
  | empty => simp [Tree.inorder] at neighbor
  | @left left right root index keys route ih =>
      simp only [Tree.inorder,List.append_assoc,List.singleton_append] at neighbor
      by_cases inside : index < left.size
      · rw [List.getElem?_append_left (by simpa only [Tree.length_inorder] using inside)] at neighbor
        exact List.mem_cons_of_mem root (ih neighbor)
      · have boundary : index = left.size := by have := route.bound; omega
        rw [boundary] at neighbor
        rw [List.getElem?_append_right (by rw [Tree.length_inorder])] at neighbor
        simp only [Tree.length_inorder, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at neighbor
        subst key
        exact List.mem_cons_self
  | @right left right root index keys route ih =>
      simp only [Tree.inorder,List.append_assoc,List.singleton_append] at neighbor
      rw [List.getElem?_append_right (by simp [Tree.length_inorder]; omega)] at neighbor
      have shifted : left.size+1+index-left.inorder.length = index+1 := by
        rw [Tree.length_inorder]
        omega
      simp only [shifted,List.getElem?_cons_succ] at neighbor
      exact List.mem_cons_of_mem root (ih neighbor)

/-- The inorder key immediately to the left of a gap is an actual ancestor
on the gap's search path. A first gap has no such key. -/
theorem GapRoute.lower {tree : RawTree α} {index : Nat} {keys : List α} (route : GapRoute tree index keys)
    {position : Nat} {key : α} (next : index = position+1)
    (neighbor : tree.inorder[position]? = some key) : key ∈ keys := by
  induction route generalizing position with
  | empty => omega
  | @left left right root index keys route ih =>
      have inside : position < left.inorder.length := by
        rw [Tree.length_inorder]
        have := route.bound
        omega
      simp only [Tree.inorder,List.append_assoc,List.singleton_append] at neighbor
      rw [List.getElem?_append_left inside] at neighbor
      exact List.mem_cons_of_mem root (ih next neighbor)
  | @right left right root index keys route ih =>
      cases index with
      | zero =>
          have boundary : position = left.size := by omega
          simp only [Tree.inorder,List.append_assoc,List.singleton_append,boundary] at neighbor
          rw [List.getElem?_append_right (by rw [Tree.length_inorder])] at neighbor
          simp only [Tree.length_inorder,Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at neighbor
          subst key
          exact List.mem_cons_self
      | succ index =>
          have positionEq : position = left.size+1+index := by omega
          simp only [Tree.inorder,List.append_assoc,List.singleton_append,positionEq] at neighbor
          rw [List.getElem?_append_right (by simp [Tree.length_inorder]; omega)] at neighbor
          have shifted : left.size+1+index-left.inorder.length = index+1 := by
            rw [Tree.length_inorder]
            omega
          simp only [shifted,List.getElem?_cons_succ] at neighbor
          exact List.mem_cons_of_mem root (ih rfl neighbor)

/-- A concrete marked rooted hull for the path. No off-path physical subtree
is traversed or altered. The hull has precisely one node per route key. -/
theorem GapRoute.hull {tree : RawTree α} {index : Nat} {keys : List α}
    (route : GapRoute tree index keys) :
    ∃ hull : MarkedTree α, hull.erase = tree ∧ hull.skeleton.size = keys.length ∧
      ∀ key, key ∈ hull.skeleton.inorder ↔ key ∈ keys := by
  induction route with
  | empty => exact ⟨.hole .empty,rfl,rfl,by simp [MarkedTree.skeleton,Tree.inorder]⟩
  | @left left right root index keys route ih =>
      obtain ⟨hull,erase,size,members⟩ := ih
      refine ⟨.node hull root (.hole right),by simp [MarkedTree.erase,erase],?_,?_⟩
      · simp [MarkedTree.skeleton,Tree.size,size,Nat.add_comm]
      · intro key
        simp [MarkedTree.skeleton,Tree.inorder,members,or_comm]
  | @right left right root index keys route ih =>
      obtain ⟨hull,erase,size,members⟩ := ih
      refine ⟨.node (.hole left) root hull,by simp [MarkedTree.erase,erase],?_,?_⟩
      · simp [MarkedTree.skeleton,Tree.size,size,Nat.add_comm]
      · intro key
        simp [MarkedTree.skeleton,Tree.inorder,members]

end MultiSplay.ComparatorGuard
