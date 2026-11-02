import MultiSplay.EndpointEncoding
import DynamicOptimality.Basic
import Mathlib.Data.List.Lex

/-!
# Addresses of actual reference BST nodes

`Before` is inorder comparison of node addresses: every left descendant comes
before its parent, every right descendant after it, and common prefixes preserve
the comparison. The addresses are computed from the shared indexed BST, rather
than supplied as an unverified labeling. The endpoint copies respect this order.
-/

namespace MultiSplay.EndpointEncoding

open ChaCha.Primary (Key)
open DynamicOptimality (BST)

inductive Before : Key → Key → Prop
  | left (tail : Key) : Before (false :: tail) []
  | right (tail : Key) : Before [] (true :: tail)
  | separate (a b : Key) : Before (false :: a) (true :: b)
  | descend (side : Bool) {a b : Key} (less : Before a b) : Before (side :: a) (side :: b)

def nodeAddress : {lower upper : Nat} → BST lower upper → Nat → Key
  | _, _, .empty _, _ => []
  | _, _, .node (root := root) l r, key =>
      if key = root then []
      else if key < root then false :: nodeAddress l key
      else true :: nodeAddress r key

theorem nodeAddress_length_lt {lower upper key : Nat} (reference : BST lower upper)
    (lo : lower ≤ key) (hi : key < upper) :
    (nodeAddress reference key).length < reference.height := by
  induction reference with
  | empty boundary => omega
  | @node lower root upper l r ihl ihr =>
      by_cases atRoot : key = root
      · simp [nodeAddress, atRoot, Splay.Tree.BST.height]
      · by_cases inLeft : key < root
        · have child := ihl lo inLeft
          simp only [nodeAddress, if_neg atRoot, if_pos inLeft, List.length_cons, Splay.Tree.BST.height]
          omega
        · have child := ihr (by omega) hi
          simp only [nodeAddress, if_neg atRoot, if_neg inLeft, List.length_cons, Splay.Tree.BST.height]
          omega

theorem nodeAddress_before {lower upper x y : Nat} (reference : BST lower upper)
    (lo : lower ≤ x) (hi : y < upper) (less : x < y) :
    Before (nodeAddress reference x) (nodeAddress reference y) := by
  induction reference with
  | empty boundary => omega
  | @node lower root upper l r ihl ihr =>
      by_cases xRoot : x = root
      · have yRoot : y ≠ root := by omega
        have yRight : ¬ y < root := by omega
        simp only [nodeAddress, if_pos xRoot, if_neg yRoot, if_neg yRight]
        exact .right _
      · by_cases yRoot : y = root
        · have xLeft : x < root := by omega
          simp only [nodeAddress, if_neg xRoot, if_pos yRoot, if_pos xLeft]
          exact .left _
        · by_cases xLeft : x < root
          · by_cases yLeft : y < root
            · simp only [nodeAddress, if_neg xRoot, if_neg yRoot, if_pos xLeft, if_pos yLeft]
              exact .descend false (ihl lo yLeft)
            · simp only [nodeAddress, if_neg xRoot, if_neg yRoot, if_pos xLeft, if_neg yLeft]
              exact .separate _ _
          · have yRight : ¬ y < root := by omega
            simp only [nodeAddress, if_neg xRoot, if_neg yRoot, if_neg xLeft, if_neg yRight]
            exact .descend true (ihr (by omega) hi)

theorem copy_cons (height : Nat) (side edge : Bool) (address : Key) :
    copy (height + 1) (edge :: address) side = edge :: edge :: copy height address side := by
  simp [copy, core]

private theorem prefix_lt (front : Key) {a b : Key} (less : a < b) :
    front ++ a < front ++ b := by
  induction front with
  | nil => exact less
  | cons x xs ih => exact List.Lex.cons ih

theorem copy_false_lt_true (height : Nat) (address : Key) :
    copy height address false < copy height address true := by
  simp only [copy, List.append_assoc, List.cons_append, List.nil_append]
  apply prefix_lt
  exact List.Lex.rel (by decide : false < true)

theorem copy_before {a b : Key} (less : Before a b) {height : Nat}
    (aInside : a.length < height) (bInside : b.length < height) :
    copy height a true < copy height b false := by
  induction less generalizing height with
  | left tail =>
      cases height with
      | zero => omega
      | succ height =>
          rw [copy_cons]
          exact List.Lex.cons (List.Lex.rel (by decide : false < true))
  | right tail =>
      cases height with
      | zero => omega
      | succ height =>
          rw [copy_cons]
          exact List.Lex.cons (List.Lex.rel (by decide : false < true))
  | separate a b =>
      cases height with
      | zero => omega
      | succ height =>
          rw [copy_cons, copy_cons]
          exact List.Lex.rel (by decide : false < true)
  | descend side less ih =>
      cases height with
      | zero => omega
      | succ height =>
          rw [copy_cons, copy_cons]
          have h := ih (height := height) (by simpa using aInside) (by simpa using bInside)
          exact List.Lex.cons (List.Lex.cons h)

/-- Any actual reference BST supplies an ordered two-copy alphabet at the
reference height. No comparison-cost premise is involved. -/
theorem reference_copies_between {n x y : Nat} (reference : BST 0 n)
    (xInside : x < n) (yInside : y < n) (less : x < y) :
    copy reference.height (nodeAddress reference x) true <
      copy reference.height (nodeAddress reference y) false :=
  copy_before (nodeAddress_before reference (Nat.zero_le _) yInside less)
    (nodeAddress_length_lt reference (Nat.zero_le _) xInside)
    (nodeAddress_length_lt reference (Nat.zero_le _) yInside)

end MultiSplay.EndpointEncoding
