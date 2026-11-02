import ChaCha.Paper20261030.RobustBSTLowerBound
import Mathlib.Tactic.NormNum

/-! A repeated-key boundary case for the manuscript's cited sharp rectangle
inequality. The four requests 5,0,10,5 admit five ordinary independent
input-free rectangles and an ordinary pointer execution of cost six.
Thus the exact inequality `rectangleBound + 2*m <= 2*pointerCost` does
not hold with the manuscript's open-corner definition and repeated keys.
This does not refute an asymptotic independent-rectangle lower bound. -/

namespace ChaCha.Paper20261030.Rectangles.RepeatedKeyExample

def points : Finset Point := {(5,0),(0,1),(10,2),(5,3)}
def family : Finset Rectangle := {
  ((5,0),(0,1)), ((5,0),(10,2)), ((0,1),(10,2)),
  ((0,1),(5,3)), ((10,2),(5,3))}

theorem family_independent : IndependentFamily points family := by
  constructor
  · intro r member
    simp only [family,Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [InputFree,On,points,Contains]
  · intro r member s other different
    simp only [family,Finset.mem_insert,Finset.mem_singleton] at member other
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals rcases other with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact False.elim (different rfl)
      | (constructor <;> intro p corner interior <;>
         rcases p with ⟨x,time⟩ <;>
         simp only [Corner,Interior] at corner interior <;>
         norm_num at corner interior <;> omega)

theorem family_card : family.card = 5 := by decide

def tree : MTR.Tree Int := .node (.node .empty 0 .empty) 5 (.node .empty 10 .empty)

theorem ordered : tree.Ordered := by norm_num [tree,MTR.Tree.Ordered,MTR.Tree.inorder]

theorem execution : MTR.Pointer.Execution tree [5,0,10,5] tree 6 := by
  apply MTR.Pointer.Execution.cons (cost := 1) (restCost := 5)
  · exact ⟨.atRoot tree,rfl,.serve rfl (.nil _)⟩
  apply MTR.Pointer.Execution.cons (cost := 2) (restCost := 3)
  · exact ⟨_,rfl,.step (.left _ _ _ _ _ _) (.serve rfl (.nil _))⟩
  apply MTR.Pointer.Execution.cons (cost := 2) (restCost := 1)
  · exact ⟨_,rfl,.step (.right _ _ _ _ _ _) (.serve rfl (.nil _))⟩
  apply MTR.Pointer.Execution.cons (cost := 1) (restCost := 0)
  · exact ⟨.atRoot tree,rfl,.serve rfl (.nil _)⟩
  exact .nil _

theorem sharp_pointer_inequality_fails :
    2*6 < rectangleBound (accessPoints [5,0,10,5]) + 2*([5,0,10,5] : List Int).length := by
  have lower := independent_card_le family_independent
  rw [family_card] at lower
  have same : accessPoints [5,0,10,5] = points := by decide
  rw [same]
  norm_num
  omega

end ChaCha.Paper20261030.Rectangles.RepeatedKeyExample
