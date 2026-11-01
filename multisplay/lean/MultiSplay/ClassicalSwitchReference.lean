import MultiSplay.ClassicalSwitchSpine
import MultiSplay.ClassicalSwitchSchedule
import MultiSplay.ReferenceAddresses

/-!
# Reference-derived preferred components and guard spines

`preferred` retains precisely the currently preferred reference path, on the
same original keys. `Path` is a traversal through actual reference children
whose edges agree with the current preference state. Its spine records those
actual ancestors, so its two guards are derived rather than supplied.
-/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree BST)
open TangoSquared.MTR.Tree (inorder Ordered size)
open TangoSquared.Primary (Key branch)
open EndpointEncoding

variable {α : Type*}

def preferred : State → RawTree α → RawTree α
  | _, .empty => .empty
  | state, .node left key right =>
      if state [] then .node .empty key (preferred (below state true) right)
      else .node (preferred (below state false) left) key .empty

def restrict (state : State) : Key → State
  | [] => state
  | edge :: rest => restrict (below state edge) rest

theorem restrict_eq (state : State) (address owner : Key) :
    restrict state address owner = state (address ++ owner) := by
  induction address generalizing state with
  | nil => rfl
  | cons edge rest ih => simpa only [restrict, below, List.cons_append] using ih (below state edge)

theorem preferred_sublist (state : State) (reference : RawTree α) :
    (inorder (preferred state reference)).Sublist (inorder reference) := by
  induction reference generalizing state with
  | empty => exact .refl _
  | node left key right ihl ihr =>
      cases side : state [] with
      | false =>
          simpa only [preferred, side, Bool.false_eq_true, ↓reduceIte, inorder, List.append_nil] using
            ((ihl (below state false)).append (List.Sublist.refl [key])).append
              (List.nil_sublist (inorder right))
      | true =>
          simpa only [preferred, side, ↓reduceIte, inorder, List.nil_append] using
            ((List.nil_sublist (inorder left)).append (List.Sublist.refl [key])).append
              (ihr (below state true))

theorem preferred_ordered [LinearOrder α] (state : State) {reference : RawTree α}
    (ordered : Ordered reference) : Ordered (preferred state reference) :=
  ordered.sublist (preferred_sublist state reference)

theorem preferred_size_le_height {lower upper : Nat} (state : State) (reference : BST lower upper) :
    size (preferred state reference.toRaw) ≤ reference.height := by
  induction reference generalizing state with
  | empty => simp [DynamicOptimality.BST.toRaw, preferred, size, Splay.Tree.BST.height]
  | node left right ihl ihr =>
      have hl := ihl (below state false)
      have hr := ihr (below state true)
      cases side : state [] <;>
        simp only [DynamicOptimality.BST.toRaw, preferred, side, Bool.false_eq_true, ↓reduceIte,
          size, Nat.zero_add, Nat.add_zero, Splay.Tree.BST.height] <;> omega

inductive Path : State → RawTree α → Key → Spine α → RawTree α → Prop
  | here (state : State) (reference : RawTree α) : Path state reference [] [] reference
  | left {state : State} {left right focus : RawTree α} {key : α} {address : Key} {spine : Spine α}
      (agrees : state [] = false)
      (rest : Path (below state false) left address spine focus) :
      Path state (.node left key right) (false::address) (spine ++ [(false,key)]) focus
  | right {state : State} {left right focus : RawTree α} {key : α} {address : Key} {spine : Spine α}
      (agrees : state [] = true)
      (rest : Path (below state true) right address spine focus) :
      Path state (.node left key right) (true::address) (spine ++ [(true,key)]) focus

theorem Path.preferred_eq {state : State} {reference focus : RawTree α} {address : Key} {spine : Spine α}
    (path : Path state reference address spine focus) :
    preferred state reference = spine.plug (preferred (restrict state address) focus) := by
  induction path with
  | here => rfl
  | left agrees rest ih => simp [preferred, agrees, restrict, Spine.plug_append, ih]
  | right agrees rest ih => simp [preferred, agrees, restrict, Spine.plug_append, ih]

theorem Path.address {state : State} {reference focus : RawTree α} {address : Key} {spine : Spine α}
    (path : Path state reference address spine focus) :
    (spine.map Prod.fst).reverse = address := by
  induction path with
  | here => rfl
  | left agrees rest ih => simp [List.map_append, List.reverse_append, ih]
  | right agrees rest ih => simp [List.map_append, List.reverse_append, ih]

theorem below_toggle_cons (state : State) (edge : Bool) (address : Key) :
    below (toggle state (edge::address)) edge = toggle (below state edge) address := by
  funext owner
  simp [below, toggle]

theorem below_toggle_empty (state : State) (edge : Bool) :
    below (toggle state []) edge = below state edge := by
  funext owner
  simp [below, toggle]

theorem restrict_toggle (state : State) (address : Key) :
    restrict (toggle state address) address = toggle (restrict state address) [] := by
  funext owner
  simp [restrict_eq, toggle]

theorem Path.toggle_endpoint {state : State} {reference focus : RawTree α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine focus) :
    Path (toggle state address) reference address spine focus := by
  induction path with
  | here => exact .here _ _
  | left agrees rest ih =>
      apply Path.left (by simpa [toggle] using agrees)
      simpa only [below_toggle_cons] using ih
  | right agrees rest ih =>
      apply Path.right (by simpa [toggle] using agrees)
      simpa only [below_toggle_cons] using ih

def tail (state : State) (side : Bool) : RawTree α → RawTree α
  | .empty => .empty
  | .node left _ right => if side then preferred (below state true) right
      else preferred (below state false) left

theorem Path.before {state : State} {reference left right : RawTree α} {pivot : α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine (.node left pivot right)) :
    preferred state reference = Spine.before (state address) spine
      (tail (restrict state address) (state address) (.node left pivot right)) pivot := by
  rw [path.preferred_eq]
  have atRoot : restrict state address [] = state address := by simp [restrict_eq]
  cases side : state address <;> simp [preferred, atRoot, side, Spine.before, tail]

theorem Path.after {state : State} {reference left right : RawTree α} {pivot : α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine (.node left pivot right)) :
    preferred (toggle state address) reference = Spine.before (!(state address)) spine
      (tail (restrict state address) (!(state address)) (.node left pivot right)) pivot := by
  rw [path.toggle_endpoint.preferred_eq, restrict_toggle]
  have atRoot : restrict state address [] = state address := by simp [restrict_eq]
  cases side : state address <;>
    simp [preferred, toggle, atRoot, side, Spine.before, tail, below_toggle_empty]

theorem RootPreferred.head {state : State} {edge : Bool} {rest : Key}
    (path : RootPreferred state (edge::rest)) : state [] = edge :=
  path [] edge (by simp [branch])

theorem RootPreferred.below {state : State} {edge : Bool} {rest : Key}
    (path : RootPreferred state (edge::rest)) : RootPreferred (below state edge) rest := by
  intro owner side direction
  apply path (edge::owner) side
  simpa [branch, List.cons_prefix_cons] using direction

/-- Every requested original key on the root preferred path has an actual
reference-derived spine. This is total on the shared indexed BST universe. -/
theorem path_exists {lower upper key : Nat} (reference : BST lower upper)
    (lo : lower ≤ key) (hi : key < upper) (state : State)
    (follows : RootPreferred state (nodeAddress reference key)) :
    ∃ spine left right,
      Path state reference.toRaw (nodeAddress reference key) spine (.node left key right) := by
  induction reference generalizing state with
  | empty => omega
  | @node lower root upper left right ihl ihr =>
      by_cases atRoot : key = root
      · subst key
        exact ⟨[],DynamicOptimality.BST.toRaw left,DynamicOptimality.BST.toRaw right,
          by simpa [nodeAddress, DynamicOptimality.BST.toRaw] using
            Path.here state (DynamicOptimality.BST.toRaw (.node left right))⟩
      · by_cases inLeft : key < root
        · have followsLeft : RootPreferred state (false::nodeAddress left key) := by
            simpa only [nodeAddress, if_neg atRoot, if_pos inLeft] using follows
          obtain ⟨spine,l,r,path⟩ := ihl lo inLeft (below state false) followsLeft.below
          exact ⟨spine++[(false,root)],l,r,by
            simpa only [DynamicOptimality.BST.toRaw, nodeAddress, if_neg atRoot, if_pos inLeft] using
              Path.left (right := DynamicOptimality.BST.toRaw right) followsLeft.head path⟩
        · have followsRight : RootPreferred state (true::nodeAddress right key) := by
            simpa only [nodeAddress, if_neg atRoot, if_neg inLeft] using follows
          obtain ⟨spine,l,r,path⟩ := ihr (by omega) hi (below state true) followsRight.below
          exact ⟨spine++[(true,root)],l,r,by
            simpa only [DynamicOptimality.BST.toRaw, nodeAddress, if_neg atRoot, if_neg inLeft] using
              Path.right (left := DynamicOptimality.BST.toRaw left) followsRight.head path⟩

end MultiSplay.ClassicalSwitch
