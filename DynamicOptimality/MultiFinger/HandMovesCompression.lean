import DynamicOptimality.MultiFinger.HandMovesAnchored
import DynamicOptimality.MultiFinger.SteinerMarked

/-! # Compression under a single added source mark -/

namespace DynamicOptimality.MultiFinger.Hand

open ChaCha.MTR

variable {α : Type*}

theorem compress_congr {first last : α → Bool} (tree : RawTree α)
    (same : ∀ key ∈ tree.inorder, first key = last key) :
    compress first tree = compress last tree := by
  induction tree with
  | empty => rfl
  | node left root right ihl ihr =>
      have rootSame := same root (by simp [Tree.inorder])
      have leftSame := ihl (fun key member => same key (by simp [Tree.inorder, member]))
      have rightSame := ihr (fun key member => same key (by simp [Tree.inorder, member]))
      simp only [compress, rootSame, leftSame, rightSame]

theorem compress_nonempty (marked : α → Bool) (tree : RawTree α) {key : α}
    (member : key ∈ tree.inorder) (hit : marked key = true) :
    (compress marked tree).nonempty = true := by
  have retained := Steiner.retains marked tree member hit
  rw [← compress_core] at retained
  cases shape : compress marked tree <;> simp_all only [core, nonempty, Tree.inorder, List.not_mem_nil]

variable [DecidableEq α]

def addMark (marked : α → Bool) (target : α) (key : α) : Bool :=
  marked key || decide (key = target)

@[simp] theorem addMark_self (marked : α → Bool) (target : α) :
    addMark marked target target = true := by simp [addMark]

theorem addMark_ne (marked : α → Bool) {target key : α} (different : key ≠ target) :
    addMark marked target key = marked key := by simp [addMark, different]

theorem addMark_existing (marked : α → Bool) {target : α} (hit : marked target = true) :
    addMark marked target = marked := by
  funext key
  by_cases same : key = target
  · subst key; simp [addMark, hit]
  · exact addMark_ne marked same

theorem addMark_comm (marked : α → Bool) (first last : α) :
    addMark (addMark marked first) last = addMark (addMark marked last) first := by
  funext key
  simp only [addMark, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

theorem compress_add_absent (marked : α → Bool) {target : α} (tree : RawTree α)
    (absent : target ∉ tree.inorder) :
    compress (addMark marked target) tree = compress marked tree := by
  apply compress_congr tree
  intro key member
  exact addMark_ne marked (fun same => absent (same ▸ member))

theorem root_mark (marked : Bool) (left : Hand α) (key : α) (right : Hand α) :
    EndpointChange (assemble marked left key right) (assemble true left key right) := by
  cases marked with
  | true => exact Or.inl rfl
  | false =>
      cases left with
      | stump a =>
          cases right with
          | stump b => exact Or.inr (.stump a b key)
          | node frames front child back => exact Or.inr (.outer_right frames front back child key a)
      | node frames front child back =>
          cases right with
          | stump b => exact Or.inr (.outer_left frames front back child key b)
          | node otherFrames otherFront otherKey otherBack => exact Or.inl rfl

/-- Retaining a core root permits arbitrary endpoint edits in a child. -/
theorem AnchoredChange.assemble_left {before after : Hand α}
    (change : AnchoredChange before after) (first : before.nonempty = true)
    (last : after.nonempty = true) (marked : Bool) (key : α) (right : Hand α) :
    AnchoredChange (assemble marked before key right) (assemble marked after key right) := by
  cases marked with
  | true => exact change.endpoint.left [] key right
  | false =>
      cases side : right.nonempty with
      | false => simpa only [assemble, first, last, side, Bool.false_or, Bool.true_and,
          Bool.false_eq_true, if_false, if_true] using
          change.extend (.left key right.source)
      | true => simpa only [assemble, first, last, side, Bool.false_or, Bool.true_and,
          if_true] using change.endpoint.left [] key right

theorem AnchoredChange.assemble_right {before after : Hand α}
    (change : AnchoredChange before after) (first : before.nonempty = true)
    (last : after.nonempty = true) (marked : Bool) (left : Hand α) (key : α) :
    AnchoredChange (assemble marked left key before) (assemble marked left key after) := by
  cases marked with
  | true => exact change.endpoint.right [] left key
  | false =>
      cases side : left.nonempty with
      | false => simpa only [assemble, first, last, side, Bool.false_or, Bool.false_and,
          Bool.false_eq_true, if_false, if_true] using
          change.extend (.right left.source key)
      | true => simpa only [assemble, first, last, side, Bool.false_or, Bool.true_and,
          if_true] using change.endpoint.right [] left key

end DynamicOptimality.MultiFinger.Hand
