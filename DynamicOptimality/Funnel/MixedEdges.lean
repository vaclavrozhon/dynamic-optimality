import DynamicOptimality.Funnel.WarmPaths

/-! # Exact mixed-edge accounting on a search path

The potential counts physical BST edges whose two keys have different interval
labels. A search leaves all off-path attachments unchanged. The two identities
below isolate their common cost and express the remaining cost by the original
path and its two monotone side spines. They are exact equalities, before any
amortized estimate is applied.
-/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree

variable {α β : Type*} [LinearOrder α] [DecidableEq β]

def rootCharge (label : α → β) (parent : α) : Tree α → Nat
  | .empty => 0
  | .node _ key _ => if label parent = label key then 0 else 1

def mixed (label : α → β) : Tree α → Nat
  | .empty => 0
  | .node l key r => mixed label l + mixed label r +
      rootCharge label key l + rootCharge label key r

def rooted (label : α → β) (parent : α) (tree : Tree α) : Nat :=
  mixed label tree + rootCharge label parent tree

@[simp] theorem rooted_empty (label : α → β) (parent : α) :
    rooted label parent .empty = 0 := rfl

theorem rooted_node (label : α → β) (parent key : α) (l r : Tree α) :
    rooted label parent (.node l key r) =
      (if label parent = label key then 0 else 1) + rooted label key l + rooted label key r := by
  change mixed label l + mixed label r + rootCharge label key l + rootCharge label key r +
    (if label parent = label key then 0 else 1) =
    (if label parent = label key then 0 else 1) +
      (mixed label l + rootCharge label key l) + (mixed label r + rootCharge label key r)
  omega

def focus (x : α) : Tree α → Tree α
  | .empty => .empty
  | .node l a r => if x < a then focus x l else if a < x then focus x r else .node l a r

def leftChild : Tree α → Tree α
  | .empty => .empty
  | .node l _ _ => l

def rightChild : Tree α → Tree α
  | .empty => .empty
  | .node _ _ r => r

/-- Cost of all unchanged off-path edges and subtrees. -/
def hanging (label : α → β) (x : α) : Tree α → Nat
  | .empty => 0
  | .node l a r => if x < a then rooted label a r + hanging label x l
      else if a < x then rooted label a l + hanging label x r else 0

/-- Edge cost along a path, followed by its terminal hanging subtree. -/
def chainCost (label : α → β) (parent : α) : List α → Tree α → Nat
  | [], gap => rooted label parent gap
  | a :: rest, gap => (if label parent = label a then 0 else 1) + chainCost label a rest gap

/-- The original tree splits into the search chain and unchanged hanging trees. -/
theorem original_path_account (label : α → β) (x parent : α) (tree : Tree α) :
    rooted label parent tree = hanging label x tree +
      chainCost label parent (ancestors x tree) (focus x tree) := by
  induction tree generalizing parent with
  | empty => simp [hanging,ancestors,focus,chainCost]
  | node l a r ihl ihr =>
    by_cases xa : x < a
    · rw [rooted_node]
      simp only [hanging,ancestors,focus,xa,↓reduceIte,chainCost]
      have recurse :=  ihl a
      omega
    · by_cases ax : a < x
      · rw [rooted_node]
        simp only [hanging,ancestors,focus,xa,ax,↓reduceIte,chainCost]
        have recurse :=  ihr a
        omega
      · simp only [hanging,ancestors,focus,xa,ax,↓reduceIte,chainCost,zero_add]

/-- Splitting at the query changes only the two side spines. The arbitrary
boundary parents make this identity compositional under recursive descent. -/
theorem split_path_account (label : α → β) (x leftParent rightParent : α)
    (tree : Tree α) (ordered : Ordered tree) :
    rooted label leftParent (below x tree) + rooted label rightParent (above x tree) =
      hanging label x tree +
      chainCost label leftParent ((ancestors x tree).filter (fun a => decide (a < x)))
        (leftChild (focus x tree)) +
      chainCost label rightParent ((ancestors x tree).filter (fun a => decide (x < a)))
        (rightChild (focus x tree)) := by
  induction tree generalizing leftParent rightParent with
  | empty => simp [below,above,hanging,ancestors,focus,leftChild,rightChild,chainCost]
  | node l a r ihl ihr =>
    obtain ⟨ol,orr,left,right⟩ := ordered_parts ordered
    by_cases xa : x < a
    · have rightFixed : above x r = r :=
        above_eq_self x r (fun z hz => xa.trans (right z hz))
      have recurse :=  ihl leftParent a ol
      simp only [below,above,xa,not_lt_of_gt xa,↓reduceIte,rightFixed,
        rooted_node,hanging,ancestors,focus,List.filter_cons,decide_true,decide_false,
        Bool.false_eq_true,↓reduceIte,chainCost]
      omega
    · by_cases ax : a < x
      · have leftFixed : below x l = l :=
          below_eq_self x l (fun z hz => (left z hz).trans ax)
        have recurse :=  ihr a rightParent orr
        simp only [below,above,xa,ax,↓reduceIte,leftFixed,
          rooted_node,hanging,ancestors,focus,List.filter_cons,decide_true,decide_false,
          Bool.false_eq_true,↓reduceIte,chainCost]
        omega
      · have same : a = x := le_antisymm (le_of_not_gt xa) (le_of_not_gt ax)
        subst a
        have leftFixed := below_eq_self x l left
        have rightFixed := above_eq_self x r right
        simp [below,above,ancestors,hanging,focus,leftChild,rightChild,chainCost,
          leftFixed,rightFixed]

/-- The potential after the actual warm update, with no extra boundary edges. -/
theorem access_path_account (label : α → β) (x : α) (tree : Tree α)
    (ordered : Ordered tree) :
    mixed label (access x tree) = hanging label x tree +
      chainCost label x ((ancestors x tree).filter (fun a => decide (a < x)))
        (leftChild (focus x tree)) +
      chainCost label x ((ancestors x tree).filter (fun a => decide (x < a)))
        (rightChild (focus x tree)) := by
  have split := split_path_account label x x x tree ordered
  unfold access mixed
  unfold rooted at split
  omega

end DynamicOptimality.Funnel.Warm
