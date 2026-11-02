import DynamicOptimality.GeometricOnlineSimulation.Blocks
import DynamicOptimality.GeometricOnlineSimulation.Queue

/-!
# Connecting marked fragments to deque layouts

Inorder holes are kept as literal trees. Only the marked connecting keys
are rearranged. Flattening here is proof bookkeeping; the physical bound
comes from the established linear rotation theorem for equal skeletons.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR ChaCha.MTR.Pointer SearchRotation DynamicOptimality.SingleFinger

variable {α : Type*}

def markRight (first : MarkedTree α) : List (Spine.Cell α) → MarkedTree α
  | [] => first
  | (key, next) :: rest => .node first key (markRight (.hole next) rest)

def markLeft (first : MarkedTree α) : List (Spine.Cell α) → MarkedTree α
  | [] => first
  | (key, next) :: rest => markLeft (.node first key (.hole next)) rest

@[simp] theorem markRight_erase (first : MarkedTree α) (cells : List (Spine.Cell α)) :
    (markRight first cells).erase = Spine.rightSpine first.erase cells := by
  induction cells generalizing first with
  | nil => rfl
  | cons cell rest ih => cases cell; simp [markRight, MarkedTree.erase, Spine.rightSpine, ih]

@[simp] theorem markLeft_erase (first : MarkedTree α) (cells : List (Spine.Cell α)) :
    (markLeft first cells).erase = Spine.leftSpine first.erase cells := by
  induction cells generalizing first with
  | nil => rfl
  | cons cell rest ih => cases cell; simp [markLeft, MarkedTree.erase, Spine.leftSpine, ih]

@[simp] theorem markRight_holes (first : MarkedTree α) (cells : List (Spine.Cell α)) :
    (markRight first cells).holes = first.holes ++ cells.map Prod.snd := by
  induction cells generalizing first with
  | nil => simp [markRight]
  | cons cell rest ih => cases cell; simp [markRight, MarkedTree.holes, ih, List.append_assoc]

@[simp] theorem markLeft_holes (first : MarkedTree α) (cells : List (Spine.Cell α)) :
    (markLeft first cells).holes = first.holes ++ cells.map Prod.snd := by
  induction cells generalizing first with
  | nil => simp [markLeft]
  | cons cell rest ih => cases cell; simp [markLeft, MarkedTree.holes, ih, List.append_assoc]

@[simp] theorem markRight_keys (first : MarkedTree α) (cells : List (Spine.Cell α)) :
    (markRight first cells).skeleton.inorder = first.skeleton.inorder ++ cells.map Prod.fst := by
  induction cells generalizing first with
  | nil => simp [markRight]
  | cons cell rest ih =>
      cases cell
      simp [markRight, MarkedTree.skeleton, Tree.inorder, ih, List.append_assoc]

@[simp] theorem markLeft_keys (first : MarkedTree α) (cells : List (Spine.Cell α)) :
    (markLeft first cells).skeleton.inorder = first.skeleton.inorder ++ cells.map Prod.fst := by
  induction cells generalizing first with
  | nil => simp [markLeft]
  | cons cell rest ih =>
      cases cell
      simp [markLeft, MarkedTree.skeleton, Tree.inorder, ih, List.append_assoc]

def Queue.marked : Queue α → MarkedTree α
  | .gap tree => .hole tree
  | .deque layout => .node (markRight (.hole layout.gap) layout.front) layout.pivot
      (markLeft (.hole layout.afterGap) layout.back)

@[simp] theorem Queue.marked_erase (queue : Queue α) : queue.marked.erase = queue.tree := by
  cases queue <;> simp [Queue.marked, Queue.tree, MarkedTree.erase, Deque.Layout.tree]

@[simp] theorem Queue.marked_holes (queue : Queue α) :
    queue.marked.holes = queue.firstGap :: queue.cells.map Prod.snd := by
  cases queue <;> simp [Queue.marked, Queue.firstGap, Queue.cells, MarkedTree.holes,
    Deque.Layout.cells, List.append_assoc]

@[simp] theorem Queue.marked_keys (queue : Queue α) :
    queue.marked.skeleton.inorder = queue.cells.map Prod.fst := by
  cases queue <;> simp [Queue.marked, Queue.cells, MarkedTree.skeleton, Tree.inorder,
    Deque.Layout.cells, List.append_assoc]

theorem Queue.marked_size (queue : Queue α) : queue.marked.skeleton.size = queue.cells.length := by
  rw [← Tree.length_inorder, queue.marked_keys, List.length_map]

structure Chain (α : Type*) where
  first : RawTree α
  cells : List (Spine.Cell α)

def Chain.join (left right : Chain α) (key : α) : Chain α :=
  ⟨left.first, left.cells ++ (key, right.first) :: right.cells⟩

def Chain.ofMarked : MarkedTree α → Chain α
  | .hole tree => ⟨tree, []⟩
  | .node left key right => (ofMarked left).join (ofMarked right) key

theorem Chain.holes_ofMarked (marked : MarkedTree α) :
    (ofMarked marked).first :: (ofMarked marked).cells.map Prod.snd = marked.holes := by
  induction marked with
  | hole => rfl
  | node left key right ihl ihr =>
      simpa only [ofMarked, join, List.map_append, List.map_cons, List.cons_append,
        MarkedTree.holes, ← ihl, ← ihr]

theorem Chain.keys_ofMarked (marked : MarkedTree α) :
    (ofMarked marked).cells.map Prod.fst = marked.skeleton.inorder := by
  induction marked with
  | hole => rfl
  | node left key right ihl ihr =>
      simp only [ofMarked, join, List.map_append, List.map_cons, ihl, ihr,
        MarkedTree.skeleton, Tree.inorder, List.append_assoc, List.singleton_append]

def Chain.queue (chain : Chain α) : Queue α :=
  match chain.cells with
  | [] => .gap chain.first
  | (key, next) :: rest => .deque ⟨chain.first, [], key, next, rest⟩

@[simp] theorem Chain.queue_first (chain : Chain α) : chain.queue.firstGap = chain.first := by
  cases chain with
  | mk first cells => cases cells with
    | nil => rfl
    | cons cell rest => cases cell; rfl

@[simp] theorem Chain.queue_cells (chain : Chain α) : chain.queue.cells = chain.cells := by
  cases chain with
  | mk first cells => cases cells with
    | nil => rfl
    | cons cell rest => cases cell; rfl

/-- Reconfiguration of just the marked keys preserves every actual hole. -/
theorem marked_rotations (source target : MarkedTree Nat)
    (holes : source.holes = target.holes)
    (keys : source.skeleton.inorder = target.skeleton.inorder) :
    ∃ count ≤ 6 * source.skeleton.size, Rotations source.erase target.erase count := by
  have size : source.skeleton.size = target.skeleton.size := by
    simpa only [Tree.length_inorder] using congrArg List.length keys
  have arrays : source.gapArray = target.gapArray := by
    funext index
    simp only [MarkedTree.gapArray, holes]
  obtain ⟨count, bound, run⟩ := Tree.graft_simulation_linear
    source.skeleton target.skeleton keys source.gapArray 0
  have run' : Tree.RestrictedSteps count source.erase target.erase := by
    rw [source.graft_gapArray, arrays, target.graft_gapArray] at run
    exact run
  exact ⟨count, by omega, OnlineModel.restrictedSteps_to_rotations run'⟩

theorem Fragment.to_queue (fragment : Fragment Nat) :
    ∃ (queue : Queue Nat) (count : Nat),
      queue.marked.holes = fragment.marked.holes ∧
      queue.marked.skeleton.inorder = fragment.marked.skeleton.inorder ∧
      Rotations fragment.marked.erase queue.tree count ∧
      count + queue.potential ≤ 10 * fragment.marked.skeleton.size := by
  let chain := Chain.ofMarked fragment.marked
  let queue := chain.queue
  have holes : queue.marked.holes = fragment.marked.holes := by
    rw [Queue.marked_holes, Chain.queue_first, Chain.queue_cells]
    exact Chain.holes_ofMarked _
  have keys : queue.marked.skeleton.inorder = fragment.marked.skeleton.inorder := by
    rw [Queue.marked_keys, Chain.queue_cells]
    exact Chain.keys_ofMarked _
  have length : queue.cells.length = fragment.marked.skeleton.size := by
    rw [← Queue.marked_size, ← Tree.length_inorder, keys, Tree.length_inorder]
  obtain ⟨count, bound, run⟩ := marked_rotations fragment.marked queue.marked holes.symm keys.symm
  have balance := queue.potential_le
  refine ⟨queue, count, holes, keys, ?_, ?_⟩
  · simpa only [Queue.marked_erase] using run
  · rw [length] at balance
    omega

end DynamicOptimality.GeometricOnlineSimulation
