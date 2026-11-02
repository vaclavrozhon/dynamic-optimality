import DynamicOptimality.MultiFinger.Steiner

/-! A reduced hand with exact source-tree provenance.
Every suppressed unary chain is retained as a literal zipper context;
every hanging unmarked subtree is retained verbatim. Compression therefore
does not forget which source edge a future finger move traverses.
The separate physical representation will store these contexts as deques. -/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR

variable {α : Type*}

inductive Hand (α : Type*) where
  | stump (tree : RawTree α)
  | node (tendon : List (Pointer.Frame α)) (left : Hand α) (key : α) (right : Hand α)

def Hand.source : Hand α → RawTree α
  | .stump tree => tree
  | .node tendon left key right => Pointer.plug (.node left.source key right.source) tendon

def Hand.core : Hand α → RawTree α
  | .stump _ => .empty
  | .node _ left key right => .node left.core key right.core

def Hand.nonempty : Hand α → Bool
  | .stump _ => false
  | .node .. => true

/-- Extend the source context by one outer edge. Its physical compression
is an endpoint update, not a replacement of an arbitrary internal tendon. -/
def Hand.extend (frame : Pointer.Frame α) : Hand α → Hand α
  | .stump tree => .stump (Pointer.plug tree [frame])
  | .node tendon left key right => .node (tendon++[frame]) left key right

theorem plug_append (tree : RawTree α) (front back : List (Pointer.Frame α)) :
    Pointer.plug tree (front++back) = Pointer.plug (Pointer.plug tree front) back := by
  induction front generalizing tree with
  | nil => rfl
  | cons frame front ih => cases frame <;> exact ih _

@[simp] theorem Hand.extend_source (frame : Pointer.Frame α) (hand : Hand α) :
    (hand.extend frame).source = Pointer.plug hand.source [frame] := by
  cases hand <;> simp only [Hand.extend,Hand.source,plug_append]

@[simp] theorem Hand.extend_core (frame : Pointer.Frame α) (hand : Hand α) :
    (hand.extend frame).core = hand.core := by cases hand <;> rfl

@[simp] theorem Hand.present_core (hand : Hand α) : Steiner.present hand.core = hand.nonempty := by
  cases hand <;> rfl

def Hand.compress (marked : α → Bool) : RawTree α → Hand α
  | .empty => .stump .empty
  | .node left key right =>
      let a := compress marked left
      let b := compress marked right
      if marked key || (a.nonempty && b.nonempty) then .node [] a key b
      else if a.nonempty then a.extend (.left key right)
      else if b.nonempty then b.extend (.right left key)
      else .stump (.node left key right)

/-- The source representation is exact, including the order of all
suppressed left/right turns and all untouched hanging subtrees. -/
theorem Hand.compress_source (marked : α → Bool) (tree : RawTree α) :
    (compress marked tree).source = tree := by
  induction tree with
  | empty => rfl
  | node left key right ihl ihr =>
    simp only [compress]
    split
    · simp only [source,Pointer.plug,ihl,ihr]
    · split
      · simp only [extend_source,Pointer.plug,ihl]
      · split
        · simp only [extend_source,Pointer.plug,ihr]
        · rfl

/-- Exactly the marked nodes and the genuine Steiner branching vertices
remain in the reduced core. All omitted nodes remain in `source`. -/
theorem Hand.compress_core (marked : α → Bool) (tree : RawTree α) :
    (compress marked tree).core = Steiner.skeleton marked tree := by
  induction tree with
  | empty => rfl
  | node left key right ihl ihr =>
    change (if marked key || ((compress marked left).nonempty && (compress marked right).nonempty)
      then Hand.node [] (compress marked left) key (compress marked right)
      else if (compress marked left).nonempty then (compress marked left).extend (.left key right)
      else if (compress marked right).nonempty then (compress marked right).extend (.right left key)
      else Hand.stump (.node left key right)).core = _
    rw [Steiner.skeleton,Steiner.merge,← ihl,← ihr,Hand.present_core,Hand.present_core]
    split
    · rfl
    · split
      · exact extend_core _ _
      · split
        · exact extend_core _ _
        · have absent : (compress marked right).core = .empty := by
            cases shape : compress marked right <;> simp_all [Hand.nonempty,Hand.core]
          simpa only [Hand.core] using absent.symm

theorem Hand.compress_size (marked : α → Bool) (tree : RawTree α) :
    (compress marked tree).core.size ≤ 2*(tree.inorder.filter marked).length := by
  rw [compress_core]
  exact Steiner.size_le_marks marked tree

end DynamicOptimality.MultiFinger
