import TangoSquared.Paper20261030.LeafRearrangements
import TangoSquared.PointerModel

/-!
# Encoding an auxiliary key tree by its ordered record leaves

Each original key becomes one leaf. A node is represented by the
concatenation of its left tree, its own key leaf, and its right tree,
suppressing empty operands. This introduces no additional leaves. One
ordinary rotation is at most five leaf-oriented pointer operations.
-/

namespace TangoSquared.Paper20261030.LeafEncoding

open RouterProjection LeafPointer

variable {α : Type*}

def encode : MTR.Tree α → Router α
  | .empty => .empty
  | .node l k r => ((encode l).join (.leaf k)).join (encode r)

theorem encode_node_nonempty (l r : MTR.Tree α) (k : α) : encode (.node l k r) ≠ .empty :=
  join_nonempty_left (join_nonempty_right (by simp))

theorem encode_nonempty {t : MTR.Tree α} (ht : t ≠ .empty) : encode t ≠ .empty := by
  cases t with
  | empty => exact False.elim (ht rfl)
  | node l k r => exact encode_node_nonempty l r k

theorem encode_leaves (t : MTR.Tree α) : (encode t).leaves = MTR.Tree.inorder t := by
  induction t with
  | empty => rfl
  | node l k r ihl ihr =>
    simp [encode,Router.leaves,ihl,ihr,MTR.Tree.inorder,List.append_assoc]

theorem encode_full (t : MTR.Tree α) : Paper20261030.Router.Full (encode t) := by
  induction t with
  | empty => trivial
  | node l k r ihl ihr =>
    exact Paper20261030.Router.full_join (Paper20261030.Router.full_join ihl True.intro) ihr

theorem encode_rotation (a b c : MTR.Tree α) (x y : α) :
    Rearranges (encode (.node (.node a x b) y c))
      (encode (.node a x (.node b y c))) 5 := by
  let p := (encode a).join (.leaf x)
  have h₁ := join_associate (p.join (encode b)) (.leaf y) (encode c)
  have h₂ := join_associate p (encode b) ((Router.leaf y).join (encode c))
  have hn₁ : (encode b).join ((Router.leaf y).join (encode c)) ≠ .empty :=
    join_nonempty_right (join_nonempty_left (by simp))
  have hn₂ : ((encode b).join (.leaf y)).join (encode c) ≠ .empty :=
    join_nonempty_left (join_nonempty_right (by simp))
  have h₃ := (join_associate (encode b) (.leaf y) (encode c)).symm.join_right (l := p) hn₁ hn₂
  exact (h₁.trans h₂).trans h₃

def frames : List (MTR.Pointer.Frame α) → List (LeafPointer.Frame α)
  | [] => []
  | .left key .empty :: rest => .left (.leaf key) :: frames rest
  | .left key r@(.node _ _ _) :: rest => .left (.leaf key) :: .left (encode r) :: frames rest
  | .right l key :: rest => .right ((encode l).join (.leaf key)) :: frames rest

def cursor (c : MTR.Pointer.Cursor α) : LeafPointer.Cursor α :=
  ⟨encode c.focus,frames c.ancestors⟩

theorem encode_left (l r : MTR.Tree α) (key : α) (rest : List (MTR.Pointer.Frame α))
    (hl : l ≠ .empty) :
    ∃ cost, Trace (some (cursor ⟨.node l key r,rest⟩))
      (some (cursor ⟨l,.left key r :: rest⟩)) cost ∧ cost ≤ 2 := by
  classical
  have hlp := encode_nonempty hl
  cases r with
  | empty =>
    change ∃ cost, Trace (some ⟨((encode l).join (.leaf key)).join .empty,frames rest⟩)
      (some ⟨encode l,.left (.leaf key) :: frames rest⟩) cost ∧ cost ≤ 2
    rw [Router.join_empty,join_eq_fork hlp (by simp)]
    exact ⟨1,.step (.nav (.left _ _ _ hlp)) (.nil _),by decide⟩
  | node rl rk rr =>
    have hrp := encode_node_nonempty rl rr rk
    have hprefix := join_nonempty_right (a := encode l) (by simp : (Router.leaf key) ≠ .empty)
    change ∃ cost, Trace (some ⟨((encode l).join (.leaf key)).join (encode (.node rl rk rr)),frames rest⟩)
      (some ⟨encode l,.left (.leaf key) :: .left (encode (.node rl rk rr)) :: frames rest⟩) cost ∧ cost ≤ 2
    rw [join_eq_fork hprefix hrp,join_eq_fork hlp (by simp)]
    exact ⟨2,.step (.nav (.left _ _ _ (by simp)))
      (.step (.nav (.left _ _ _ hlp)) (.nil _)),le_rfl⟩

theorem encode_right (l r : MTR.Tree α) (key : α) (rest : List (MTR.Pointer.Frame α))
    (hr : r ≠ .empty) :
    ∃ cost, Trace (some (cursor ⟨.node l key r,rest⟩))
      (some (cursor ⟨r,.right l key :: rest⟩)) cost ∧ cost ≤ 2 := by
  classical
  have hrp := encode_nonempty hr
  have hprefix := join_nonempty_right (a := encode l) (by simp : (Router.leaf key) ≠ .empty)
  change ∃ cost, Trace (some ⟨((encode l).join (.leaf key)).join (encode r),frames rest⟩)
      (some ⟨encode r,.right ((encode l).join (.leaf key)) :: frames rest⟩) cost ∧ cost ≤ 2
  rw [join_eq_fork hprefix hrp]
  exact ⟨1,.step (.nav (.right _ _ _ hrp)) (.nil _),by decide⟩

theorem encode_plug (focus : MTR.Tree α) (rest : List (MTR.Pointer.Frame α))
    (hf : focus ≠ .empty) :
    LeafPointer.plug (encode focus) (frames rest) = encode (MTR.Pointer.plug focus rest) := by
  classical
  induction rest generalizing focus with
  | nil => rfl
  | cons frame rest ih =>
    have hfp := encode_nonempty hf
    cases frame with
    | left key r =>
      have hh := ih (.node focus key r) (by simp)
      have hprefix := join_nonempty_right (a := encode focus) (by simp : (Router.leaf key) ≠ .empty)
      cases r with
      | empty =>
        simpa only [frames,LeafPointer.plug,MTR.Pointer.plug,encode,Router.join_empty,
          join_eq_fork hfp (by simp : (Router.leaf key) ≠ .empty)] using hh
      | node rl rk rr =>
        have hrp := encode_node_nonempty rl rr rk
        change LeafPointer.plug (((encode focus).join (.leaf key)).join (encode (.node rl rk rr)))
          (frames rest) = _ at hh
        rw [join_eq_fork hprefix hrp,join_eq_fork hfp (by simp)] at hh
        exact hh
    | right l key =>
      have hh := ih (.node l key focus) (by simp)
      have hprefix := join_nonempty_right (a := encode l) (by simp : (Router.leaf key) ≠ .empty)
      change LeafPointer.plug (((encode l).join (.leaf key)).join (encode focus)) (frames rest) = _ at hh
      rw [join_eq_fork hprefix hfp] at hh
      exact hh

theorem cursor_tree (c : MTR.Pointer.Cursor α) (hf : c.focus ≠ .empty) :
    (cursor c).tree = encode c.tree := encode_plug c.focus c.ancestors hf

theorem step_focus_nonempty {c d : MTR.Pointer.Cursor α} (h : MTR.Pointer.Step c d) :
    d.focus ≠ .empty := by cases h <;> simp

theorem encode_step {c d : MTR.Pointer.Cursor α} (h : MTR.Pointer.Step c d)
    (hf : c.focus ≠ .empty) :
    ∃ cost, Trace (some (cursor c)) (some (cursor d)) cost ∧ cost ≤ 5 := by
  cases h with
  | left a b c x y rest =>
    obtain ⟨cost,trace,hcost⟩ := encode_left (.node a x b) c y rest (by simp)
    exact ⟨cost,trace,by omega⟩
  | right a b c x y rest =>
    obtain ⟨cost,trace,hcost⟩ := encode_right a (.node b y c) x rest (by simp)
    exact ⟨cost,trace,by omega⟩
  | upLeft a b x rest =>
    obtain ⟨cost,trace,hcost⟩ := encode_left a b x rest hf
    exact ⟨cost,trace.reverse,by omega⟩
  | upRight a b x rest =>
    obtain ⟨cost,trace,hcost⟩ := encode_right a b x rest hf
    exact ⟨cost,trace.reverse,by omega⟩
  | rotateRight a b c x y rest => exact encode_rotation a b c x y (frames rest)
  | rotateLeft a b c x y rest => exact (encode_rotation a b c x y).symm (frames rest)

/-- A movement/rotation trace on the auxiliary key tree has a leaf-oriented
realization with constant overhead and exactly the original record leaves. -/
theorem encode_trace {c d : MTR.Pointer.Cursor α} {cost : Nat}
    (h : MTR.Pointer.Trace c [] d cost) (hf : c.focus ≠ .empty) :
    ∃ leafCost, Trace (some (cursor c)) (some (cursor d)) leafCost ∧ leafCost ≤ 5 * cost := by
  cases h with
  | nil => exact ⟨0,.nil _,by omega⟩
  | step move rest =>
    obtain ⟨first,ht,hfirst⟩ := encode_step move hf
    obtain ⟨last,hr,hlast⟩ := encode_trace rest (step_focus_nonempty move)
    exact ⟨first + last,ht.append hr,by omega⟩
termination_by cost

end TangoSquared.Paper20261030.LeafEncoding
