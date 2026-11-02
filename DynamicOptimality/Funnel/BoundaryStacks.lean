import DynamicOptimality.Funnel.WarmCartesian

/-! # The boundary-stack deletion budget

Every request enters the maximum and minimum stack once. The identities below
prove, for arbitrary histories including repetitions, that all deletions from
either stack are paid by those insertions. Their total is at most twice the
number of requests, starting from empty stacks.
-/

namespace DynamicOptimality.Funnel.Warm

variable {α : Type*} [LinearOrder α]

/-- General stack transition: retain old entries satisfying `keep`, then push. -/
def stackStep (keep : α → α → Bool) (x : α) (stack : List α) : List α :=
  x :: stack.filter (keep x)

def stackPops (keep : α → α → Bool) (x : α) (stack : List α) : Nat :=
  (stack.filter (fun y => !(keep x y))).length

/-- Requests are chronological; each stack is stored newest first. -/
def stackRun (keep : α → α → Bool) (stack : List α) : List α → List α
  | [] => stack
  | x :: word => stackRun keep (stackStep keep x stack) word

def stackCost (keep : α → α → Bool) (stack : List α) : List α → Nat
  | [] => 0
  | x :: word => stackPops keep x stack + stackCost keep (stackStep keep x stack) word

omit [LinearOrder α] in
theorem stackStep_account (keep : α → α → Bool) (x : α) (stack : List α) :
    stackPops keep x stack + (stackStep keep x stack).length = stack.length + 1 := by
  have split := List.length_eq_length_filter_add (l := stack) (keep x)
  simp only [stackPops,stackStep,List.length_cons]
  omega

omit [LinearOrder α] in
theorem stackRun_account (keep : α → α → Bool) (stack word : List α) :
    stackCost keep stack word + (stackRun keep stack word).length = stack.length + word.length := by
  induction word generalizing stack with
  | nil => simp [stackCost,stackRun]
  | cons x word ih =>
    have step := stackStep_account keep x stack
    have rest := ih (stackStep keep x stack)
    simp only [stackCost,stackRun,List.length_cons]
    omega

omit [LinearOrder α] in
theorem stackCost_le (keep : α → α → Bool) (stack word : List α) :
    stackCost keep stack word ≤ stack.length + word.length := by
  have account := stackRun_account keep stack word
  omega

def maximumKeep (x y : α) : Bool := decide (x < y)
def minimumKeep (x y : α) : Bool := decide (y < x)

/-- A two-stack budget available for alternative boundary-based analyses.
The completed convex composition theorem instead uses a mixed-edge potential. -/
theorem boundaryStack_budget (word : List α) :
    stackCost maximumKeep [] word + stackCost minimumKeep [] word ≤ 2 * word.length := by
  have upper := stackCost_le maximumKeep [] word
  have lower := stackCost_le minimumKeep [] word
  simp only [List.length_nil,zero_add] at upper lower
  omega

end DynamicOptimality.Funnel.Warm
