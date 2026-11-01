import MultiSplay.InitializedOnline

/-!
# Literal classical execution after the fixed initialization

The first access searches the supplied tree, performs the request-independent
initialization, and then executes the selected classical switch sequence.
The generic initialization witness retains precisely that sequence's rotation
count. Subsequent accesses preserve the canonical choices and their entire
classical chronology.
-/

namespace MultiSplay.Online

open DynamicOptimality
open EndpointEncoding ClassicalSwitch

variable {n : Nat}

/-- The first wrapper transition retains the rotation count of the very
classical transition chosen by the canonical strategy. -/
theorem first_canonicalCount (before : BST 0 n) (request : Fin n) :
    (OnlineBST.Initialization.firstStep (canonicalStrategy n) (canonicalState n) before request).canonicalCount =
      (Global.Preferred.Online.step (canonicalState n) request).rotations := by
  apply OnlineBST.Initialization.FirstTransition.canonicalCount_eq
    (depth := (canonicalState n).actual.depth request.val)
  · exact SearchRotation.toRaw_searchDepth (canonicalState n).actual (Nat.zero_le _) request.isLt
  · rfl

/-- The cost is exactly the supplied-tree search plus the fixed setup and
the literal first classical transition, with no extra canonical search. -/
theorem first_cost_eq_classical (before : BST 0 n) (request : Fin n) :
    (strategy n).accessCost (initial before) request =
      before.depth request.val + 1 +
        ((OnlineBST.Initialization.fixedInitialization (canonicalStrategy n) (canonicalState n) before).count +
          (Global.Preferred.Online.step (canonicalState n) request).rotations) := by
  change (OnlineBST.Initialization.firstStep (canonicalStrategy n) (canonicalState n) before request).cost = _
  rw [(OnlineBST.Initialization.firstStep (canonicalStrategy n) (canonicalState n) before request).exactCost,
    first_canonicalCount]

/-- A literal concatenation through the fixed canonical tree realizes exactly
the first transition's charged rotations. Its second segment is the actual
chosen classical switch execution. -/
theorem first_classical_transcript (before : BST 0 n) (request : Fin n) :
    SearchRotation.Rotations before.toRaw
      ((strategy n).tree ((strategy n).advance (initial before) request))
      ((OnlineBST.Initialization.fixedInitialization (canonicalStrategy n) (canonicalState n) before).count +
        (Global.Preferred.Online.step (canonicalState n) request).rotations) :=
  (OnlineBST.Initialization.fixedInitialization (canonicalStrategy n) (canonicalState n) before).rotations.append
    (Global.Preferred.Online.step (canonicalState n) request).classicalRun.rotations

/-- Initialization does not replace the first classical switch schedule by an
arbitrary equal-cost rotation sequence: that same schedule reaches the chosen
first output tree with its retained exact count and forest work. -/
theorem first_classical (before : BST 0 n) (request : Fin n) :
    Global.Preferred.Switches (fun _ => true) (balancedReference n).toRaw
      (actualEmissions (fun _ => true) (nodeAddress (balancedReference n) request.val))
      (balancedReference n).toRaw
      ((strategy n).tree ((strategy n).advance (initial before) request))
      (Global.Preferred.Online.step (canonicalState n) request).rotations
      (Global.Preferred.Online.step (canonicalState n) request).work :=
  (Global.Preferred.Online.step (canonicalState n) request).classicalRun

/-- Every nonempty initialized run ends in the exact canonical run's tree. -/
theorem run_tree_eq_canonical (before : BST 0 n) (request : Fin n) (rest : List (Fin n)) :
    (strategy n).tree ((strategy n).run (initial before) (request::rest)).1 =
      (canonicalStrategy n).tree ((canonicalStrategy n).run (canonicalState n) (request::rest)).1 :=
  OnlineBST.Initialization.run_tree (canonicalStrategy n) (canonicalState n) before request rest

/-- All requests after the single setup follow the canonical strategy's
literal classical chronology, including its first request and final switch. -/
theorem run_classical (before : BST 0 n) (request : Fin n) (rest : List (Fin n)) :
    Global.Preferred.Online.Requests (balancedReference n) (fun _ => true) (request::rest)
      (balancedReference n).toRaw
      ((strategy n).tree ((strategy n).run (initial before) (request::rest)).1)
      (Global.Preferred.Online.runRotations (canonicalState n) (request::rest))
      (Global.Preferred.Online.runWork (canonicalState n) (request::rest)) := by
  rw [run_tree_eq_canonical]
  exact Global.Preferred.Online.run_classical (canonicalState n) (request::rest)

end MultiSplay.Online
