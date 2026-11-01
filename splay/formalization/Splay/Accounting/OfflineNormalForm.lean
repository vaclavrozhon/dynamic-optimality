import Splay.Accounting.OfflineOptimum

namespace Splay.Accounting.OfflineNormalForm

open Splay.Tree.BST
open Splay.Assumptions.NormalForm

abbrev BST := Splay.Tree.BST

/--
An event-level presentation of an offline execution.

Unlike `ComparisonTrace`, this inductive form is convenient for construction:
a rotation changes the tree but not the request list, while a service event
consumes its rooted head request without changing the tree.
-/
inductive RootEventTrace {n : ℕ} :
    List (Fin n) → BST 0 n → BST 0 n → ℕ → Prop
  | done (tree : BST 0 n) :
      RootEventTrace [] tree tree 0
  | rotate {accesses : List (Fin n)}
      {before middle after : BST 0 n}
      {depth rotations : ℕ}
      (head : RotationAt depth before middle)
      (tail : RootEventTrace accesses middle after rotations) :
      RootEventTrace accesses before after rotations.succ
  | serve {access : Fin n} {accesses : List (Fin n)}
      {before after : BST 0 n} {rotations : ℕ}
      (root : before.HasRoot access.val)
      (tail : RootEventTrace accesses before after rotations) :
      RootEventTrace (access :: accesses) before after rotations

namespace RootEventTrace

/-- Prepending an ordinary rotation execution preserves its exact length. -/
theorem prependRotationExecution
    {n prefixRotations tailRotations : ℕ}
    {accesses : List (Fin n)}
    {before middle after : BST 0 n}
    (prefixExecution :
      RotationExecution prefixRotations before middle)
    (tail :
      RootEventTrace accesses middle after tailRotations) :
    RootEventTrace accesses before after
      (prefixRotations + tailRotations) := by
  induction prefixRotations generalizing before middle with
  | zero =>
      cases prefixExecution
      simpa using tail
  | succ length ih =>
      cases prefixExecution with
      | step head rest =>
          simpa [Nat.succ_add] using
            (RootEventTrace.rotate head
              (ih rest tail))

end RootEventTrace

namespace OfflineOptimum.Execution

/-- Every offline execution has an event trace with the same rotation count. -/
theorem toRootEventTrace
    {n rotations : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (execution :
      OfflineOptimum.Execution accesses before after rotations) :
    RootEventTrace accesses before after rotations := by
  induction execution with
  | done tree =>
      exact .done tree
  | @next access accesses before served after
      prefixRotations tailRotations prefixExecution root tail ih =>
      exact
        (RootEventTrace.serve root ih).prependRotationExecution
          prefixExecution

end OfflineOptimum.Execution

/--
The exact-count version of `ComparisonTrace`, additionally recording its
initial and final trees.  Keeping `rotations` as a type parameter makes the
event-to-indexed conversion definitionally exact.
-/
structure ExactTrace {n : ℕ}
    (accesses : List (Fin n))
    (before after : BST 0 n) (rotations : ℕ) where
  state : Fin (rotations + 1) → BST 0 n
  rotationDepth : Fin rotations → ℕ
  rotates :
    ∀ step : Fin rotations,
      RotationAt (rotationDepth step)
        (state step.castSucc) (state step.succ)
  servedAt : Fin accesses.length → Fin (rotations + 1)
  servedInOrder : Monotone servedAt
  serves :
    ∀ request : Fin accesses.length,
      (state (servedAt request)).HasRoot
        (accesses.get request).val
  initial_eq : state 0 = before
  final_eq : state (Fin.last rotations) = after

namespace ExactTrace

/-- Forgetting the endpoint equalities gives the repository trace type. -/
def toComparisonTrace
    {n rotations : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (trace : ExactTrace accesses before after rotations) :
    ComparisonTrace n accesses where
  rotationCount := rotations
  state := trace.state
  rotationDepth := trace.rotationDepth
  rotates := trace.rotates
  servedAt := trace.servedAt
  servedInOrder := trace.servedInOrder
  serves := trace.serves

@[simp]
theorem toComparisonTrace_cost
    {n rotations : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (trace : ExactTrace accesses before after rotations) :
    trace.toComparisonTrace.cost = accesses.length + rotations :=
  rfl

end ExactTrace

/-- Prefixing zero to a monotone finite map preserves monotonicity. -/
private theorem monotone_finCases_zero
    {source target : ℕ}
    {f : Fin source → Fin (target + 1)}
    (monotone : Monotone f) :
    Monotone
      (Fin.cases 0 f :
        Fin (source + 1) → Fin (target + 1)) := by
  intro left
  revert left
  refine Fin.cases ?_ (fun leftTail => ?_)
  · intro right ordered
    exact Fin.zero_le _
  · intro right
    revert right
    refine Fin.cases ?_ (fun rightTail => ?_)
    · intro ordered
      have impossible :
          leftTail.succ.val ≤
            (0 : Fin (source + 1)).val :=
        ordered
      simp at impossible
    · intro ordered
      exact monotone (by
        apply Fin.le_iff_val_le_val.mpr
        have values :
            leftTail.succ.val ≤ rightTail.succ.val :=
          ordered
        simpa using values)

/-- Applying `Fin.succ` to a monotone finite map preserves monotonicity. -/
private theorem monotone_finSucc
    {source target : ℕ}
    {f : Fin source → Fin (target + 1)}
    (monotone : Monotone f) :
    Monotone
      (fun index => (f index).succ :
        Fin source → Fin (target + 2)) := by
  intro left right ordered
  apply Fin.le_iff_val_le_val.mpr
  simpa using
    Fin.le_iff_val_le_val.mp (monotone ordered)

namespace RootEventTrace

/--
Every event trace has an exactly indexed comparison trace with the same
requests, endpoints, and rotation count.
-/
theorem exists_exactTrace
    {n rotations : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (events : RootEventTrace accesses before after rotations) :
    Nonempty (ExactTrace accesses before after rotations) := by
  induction events with
  | done tree =>
      exact
        ⟨{ state := fun _ => tree
           rotationDepth := Fin.elim0
           rotates := fun step => Fin.elim0 step
           servedAt := Fin.elim0
           servedInOrder := fun left => Fin.elim0 left
           serves := fun request => Fin.elim0 request
           initial_eq := rfl
           final_eq := rfl }⟩
  | @rotate accesses before middle after depth rotations
      head tail ih =>
      obtain ⟨tailTrace⟩ := ih
      let state : Fin (rotations.succ + 1) → BST 0 n :=
        Fin.cons before tailTrace.state
      let rotationDepth : Fin rotations.succ → ℕ :=
        Fin.cons depth tailTrace.rotationDepth
      have rotates :
          ∀ step : Fin rotations.succ,
            RotationAt (rotationDepth step)
              (state step.castSucc) (state step.succ) := by
        intro step
        refine Fin.cases ?_ (fun tailStep => ?_) step
        · simpa [state, rotationDepth, tailTrace.initial_eq]
            using head
        · simpa [state, rotationDepth] using
            tailTrace.rotates tailStep
      let servedAt :
          Fin accesses.length → Fin (rotations.succ + 1) :=
        fun request => (tailTrace.servedAt request).succ
      have serves :
          ∀ request : Fin accesses.length,
            (state (servedAt request)).HasRoot
              (accesses.get request).val := by
        intro request
        simpa [state, servedAt] using tailTrace.serves request
      exact
        ⟨{ state := state
           rotationDepth := rotationDepth
           rotates := rotates
           servedAt := servedAt
           servedInOrder :=
             monotone_finSucc tailTrace.servedInOrder
           serves := serves
           initial_eq := by simp [state]
           final_eq := by
             simpa [state] using tailTrace.final_eq }⟩
  | @serve access accesses before after rotations root tail ih =>
      obtain ⟨tailTrace⟩ := ih
      let servedAt :
          Fin (access :: accesses).length →
            Fin (rotations + 1) :=
        Fin.cases 0 tailTrace.servedAt
      have serves :
          ∀ request : Fin (access :: accesses).length,
            (tailTrace.state (servedAt request)).HasRoot
              ((access :: accesses).get request).val := by
        intro request
        refine Fin.cases ?_ (fun tailRequest => ?_) request
        · change (tailTrace.state 0).HasRoot access.val
          rw [tailTrace.initial_eq]
          exact root
        · simpa [servedAt] using tailTrace.serves tailRequest
      exact
        ⟨{ state := tailTrace.state
           rotationDepth := tailTrace.rotationDepth
           rotates := tailTrace.rotates
           servedAt := servedAt
           servedInOrder :=
             monotone_finCases_zero tailTrace.servedInOrder
           serves := serves
           initial_eq := tailTrace.initial_eq
           final_eq := tailTrace.final_eq }⟩

end RootEventTrace

namespace OfflineOptimum.Execution

/--
An offline execution can be flattened into an exact repository comparison
trace without changing its request or rotation count.
-/
theorem exists_exactTrace
    {n rotations : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (execution :
      OfflineOptimum.Execution accesses before after rotations) :
    Nonempty (ExactTrace accesses before after rotations) :=
  RootEventTrace.exists_exactTrace
    (OfflineOptimum.Execution.toRootEventTrace execution)

end OfflineOptimum.Execution

/--
The offline optimum is attained by a `ComparisonTrace`, not merely by the
more construction-friendly inductive execution type.
-/
theorem exists_optimalComparisonTrace
    {n : ℕ} (accesses : List (Fin n)) :
    ∃ trace : ComparisonTrace n accesses,
      trace.cost = OfflineOptimum.offlineOptCost accesses := by
  obtain ⟨initial, final, rotations, execution, cost_eq⟩ :=
    OfflineOptimum.exists_optimalExecution_eq accesses
  obtain ⟨exactTrace⟩ :=
    OfflineOptimum.Execution.exists_exactTrace execution
  exact
    ⟨exactTrace.toComparisonTrace,
      exactTrace.toComparisonTrace_cost.trans cost_eq.symm⟩

/-- The canonical witness used by the optimum module is a full left comb. -/
@[simp]
theorem canonicalTree_height (n : ℕ) :
    (OfflineOptimum.canonicalTree n).height = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [OfflineOptimum.canonicalTree,
        Splay.Tree.BST.height, ih]

/-- An optimal empty trace whose sole state is the canonical left comb. -/
def emptyCanonicalTrace (n : ℕ) :
    ComparisonTrace n [] where
  rotationCount := 0
  state := fun _ => OfflineOptimum.canonicalTree n
  rotationDepth := Fin.elim0
  rotates := fun step => Fin.elim0 step
  servedAt := Fin.elim0
  servedInOrder := fun request => Fin.elim0 request
  serves := fun request => Fin.elim0 request

/-- The empty canonical trace really attains the offline optimum. -/
@[simp]
theorem emptyCanonicalTrace_cost (n : ℕ) :
    (emptyCanonicalTrace n).cost =
      OfflineOptimum.offlineOptCost ([] : List (Fin n)) := by
  rw [OfflineOptimum.offlineOptCost_nil]
  rfl

/--
Cost optimality alone does not supply the logarithmic-height invariant: when
the displayed numerical inequality holds, the optimal canonical empty trace
is not normal for those bounds.
-/
theorem emptyCanonicalTrace_not_normal
    (bounds : Bounds) (n : ℕ)
    (tooTall :
      bounds.heightMultiplier * Analysis.stabilizedLog n < n) :
    ¬IsNormal bounds (emptyCanonicalTrace n) := by
  intro normal
  have heightBound := normal.height_le (0 : Fin 1)
  change
    (OfflineOptimum.canonicalTree n).height ≤
      bounds.heightMultiplier * Analysis.stabilizedLog n
    at heightBound
  rw [canonicalTree_height] at heightBound
  omega

/-- Exponential universe sizes eventually beat every fixed log multiplier. -/
theorem exists_height_above_logMultiplier (multiplier : ℕ) :
    ∃ n : ℕ,
      multiplier * Analysis.stabilizedLog n < n := by
  cases multiplier with
  | zero =>
      exact
        ⟨1, by
          simp [Analysis.stabilizedLog]⟩
  | succ predecessor =>
      let multiplier := predecessor.succ
      let exponent := 2 * multiplier
      let n := 2 ^ exponent
      have multiplier_pos : 0 < multiplier := by
        simp [multiplier]
      have exponent_pos : 0 < exponent := by
        simp [exponent, multiplier_pos]
      have two_le_n : 2 ≤ n := by
        change 2 ^ 1 ≤ 2 ^ exponent
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have exponentialBound :=
        Nat.two_mul_sq_add_one_le_two_pow_two_mul multiplier
      refine ⟨n, ?_⟩
      rw [Analysis.stabilizedLog, max_eq_right two_le_n]
      rw [show n = 2 ^ exponent by rfl]
      rw [Nat.clog_pow 2 exponent (by omega)]
      change multiplier * exponent < 2 ^ exponent
      dsimp [exponent]
      nlinarith

/--
For every fixed bounds record there is an optimal trace that is not normal:
choose the empty execution on a sufficiently tall canonical tree.  Therefore
one cannot finish normal form by merely selecting an arbitrary optimal
execution; a genuine tree-representation transformation is necessary.
-/
theorem exists_optimalTrace_not_normal (bounds : Bounds) :
    ∃ (n : ℕ) (trace : ComparisonTrace n []),
      trace.cost =
          OfflineOptimum.offlineOptCost ([] : List (Fin n)) ∧
        ¬IsNormal bounds trace := by
  obtain ⟨n, tooTall⟩ :=
    exists_height_above_logMultiplier bounds.heightMultiplier
  exact
    ⟨n, emptyCanonicalTrace n, emptyCanonicalTrace_cost n,
      emptyCanonicalTrace_not_normal bounds n tooTall⟩

/--
There are no universal bounds under which every cost-optimal raw trace is
already normal.  Normalization must be allowed to replace the source trace.
-/
theorem not_all_optimalTraces_are_uniformlyNormal :
    ¬∃ bounds : Bounds,
      ∀ (n : ℕ) (accesses : List (Fin n))
        (trace : ComparisonTrace n accesses),
        trace.cost = OfflineOptimum.offlineOptCost accesses →
          IsNormal bounds trace := by
  rintro ⟨bounds, allNormal⟩
  obtain ⟨n, trace, optimal, notNormal⟩ :=
    exists_optimalTrace_not_normal bounds
  exact notNormal (allNormal n [] trace optimal)

/-- Reindex only the upper endpoint of an indexed BST. -/
private def castUpper
    {lower upper upper' : ℕ}
    (equal : upper = upper')
    (tree : BST lower upper) :
    BST lower upper' :=
  equal ▸ tree

@[simp]
private theorem castUpper_height
    {lower upper upper' : ℕ}
    (equal : upper = upper')
    (tree : BST lower upper) :
    (castUpper equal tree).height = tree.height := by
  subst upper'
  rfl

/--
Every consecutive key interval has a balanced indexed BST of upper-logarithmic
height.  This closes the height-only small case without importing an external
balanced-tree implementation.
-/
theorem exists_logHeightTree (lower size : ℕ) :
    ∃ tree : BST lower (lower + size),
      tree.height ≤ Nat.clog 2 (size + 1) := by
  induction size using Nat.strong_induction_on generalizing lower with
  | h size ih =>
      cases size with
      | zero =>
          exact
            ⟨.empty lower, by
              simp [Splay.Tree.BST.height]⟩
      | succ remaining =>
          let leftSize := remaining / 2
          let rightSize := remaining - leftSize
          have left_lt : leftSize < remaining.succ := by
            dsimp [leftSize]
            omega
          have right_lt : rightSize < remaining.succ := by
            dsimp [rightSize, leftSize]
            omega
          obtain ⟨left, leftHeight⟩ :=
            ih leftSize left_lt lower
          obtain ⟨right, rightHeight⟩ :=
            ih rightSize right_lt
              (lower + leftSize + 1)
          have upper_eq :
              (lower + leftSize + 1) + rightSize =
                lower + remaining.succ := by
            dsimp [leftSize, rightSize]
            omega
          let raw :
              BST lower
                ((lower + leftSize + 1) + rightSize) :=
            .node left right
          let tree : BST lower (lower + remaining.succ) :=
            castUpper upper_eq raw
          have leftSize_le_rightSize :
              leftSize ≤ rightSize := by
            dsimp [leftSize, rightSize]
            omega
          have rightHalf :
              rightSize + 1 = (remaining + 3) / 2 := by
            dsimp [leftSize, rightSize]
            omega
          have leftHalf :
              leftSize + 1 ≤ (remaining + 3) / 2 := by
            rw [← rightHalf]
            omega
          have leftLog :
              Nat.clog 2 (leftSize + 1) ≤
                Nat.clog 2 ((remaining + 3) / 2) :=
            Nat.clog_mono_right 2 leftHalf
          have rightLog :
              Nat.clog 2 (rightSize + 1) ≤
                Nat.clog 2 ((remaining + 3) / 2) := by
            rw [rightHalf]
          have childHeight :
              max left.height right.height ≤
                Nat.clog 2 ((remaining + 3) / 2) :=
            max_le
              (leftHeight.trans leftLog)
              (rightHeight.trans rightLog)
          have clog_step :
              Nat.clog 2 (remaining + 2) =
                Nat.clog 2 ((remaining + 3) / 2) + 1 := by
            rw [Nat.clog_of_two_le (by omega) (by omega)]
            congr 2
          refine ⟨tree, ?_⟩
          rw [show remaining.succ + 1 = remaining + 2 by omega]
          rw [clog_step]
          simpa [tree, raw, Splay.Tree.BST.height] using
            Nat.add_le_add_right childHeight 1

/-- The upper log of `n+1` is at most twice the stabilized log of `n`. -/
theorem clog_succ_le_two_stabilizedLog (n : ℕ) :
    Nat.clog 2 (n + 1) ≤ 2 * Analysis.stabilizedLog n := by
  let universeSize := max 2 n
  let logarithm := Analysis.stabilizedLog n
  have universe_two : 2 ≤ universeSize := by
    simp [universeSize]
  have n_le_universe : n ≤ universeSize := by
    simp [universeSize]
  have universe_pow :
      universeSize ≤ 2 ^ logarithm := by
    dsimp [logarithm, Analysis.stabilizedLog]
    exact Nat.le_pow_clog (by omega) universeSize
  have succ_le_pow :
      n + 1 ≤ 2 ^ (logarithm + 1) := by
    calc
      n + 1 ≤ 2 * universeSize := by omega
      _ ≤ 2 * (2 ^ logarithm) :=
        Nat.mul_le_mul_left 2 universe_pow
      _ = 2 ^ (logarithm + 1) := by
        rw [Nat.pow_succ]
        omega
  have clog_le :
      Nat.clog 2 (n + 1) ≤ logarithm + 1 :=
    Nat.clog_le_of_le_pow succ_le_pow
  have logarithm_pos : 0 < logarithm := by
    exact Analysis.stabilizedLog_pos n
  omega

/-- A chosen balanced tree on the full universe. -/
noncomputable def balancedTree (n : ℕ) : BST 0 n := by
  classical
  exact
    castUpper (Nat.zero_add n)
      (Classical.choose (exists_logHeightTree 0 n))

/-- The chosen balanced tree has the advertised logarithmic height. -/
theorem balancedTree_height_le (n : ℕ) :
    (balancedTree n).height ≤ Nat.clog 2 (n + 1) := by
  classical
  simpa [balancedTree] using
    Classical.choose_spec (exists_logHeightTree 0 n)

/-- Universal constants sufficient for the empty-request normal form. -/
def emptyBounds : Bounds where
  heightMultiplier := 2
  maxRotationDepth := 0
  costMultiplier := 1
  heightMultiplier_pos := by omega
  costMultiplier_pos := by omega

/-- A zero-cost balanced comparison trace for the empty request sequence. -/
noncomputable def emptyBalancedTrace (n : ℕ) :
    ComparisonTrace n [] where
  rotationCount := 0
  state := fun _ => balancedTree n
  rotationDepth := Fin.elim0
  rotates := fun step => Fin.elim0 step
  servedAt := Fin.elim0
  servedInOrder := fun request => Fin.elim0 request
  serves := fun request => Fin.elim0 request

/-- Empty request sequences satisfy uniform normal form unconditionally. -/
theorem emptyBalancedTrace_normal (n : ℕ) :
    IsNormal emptyBounds (emptyBalancedTrace n) := by
  constructor
  · intro time
    change (balancedTree n).height ≤
      2 * Analysis.stabilizedLog n
    exact
      (balancedTree_height_le n).trans
        (clog_succ_le_two_stabilizedLog n)
  · intro step
    exact Fin.elim0 step

/-- The empty normal trace has exactly the genuine offline optimum cost. -/
theorem exists_normalOptimalTrace_nil (n : ℕ) :
    ∃ trace : ComparisonTrace n [],
      IsNormal emptyBounds trace ∧
        trace.cost ≤
          emptyBounds.costMultiplier *
            OfflineOptimum.offlineOptCost
              ([] : List (Fin n)) := by
  refine
    ⟨emptyBalancedTrace n, emptyBalancedTrace_normal n, ?_⟩
  rw [OfflineOptimum.offlineOptCost_nil]
  rfl

/--
For every key there is a logarithmic-height indexed tree having that key at
the root.  The two sides are independently balanced.
-/
theorem exists_rootedLogHeightTree
    {n : ℕ} (key : Fin n) :
    ∃ tree : BST 0 n,
      tree.HasRoot key.val ∧
        tree.height ≤ Nat.clog 2 (n + 1) + 1 := by
  let leftSize := key.val
  let rightSize := n - (key.val + 1)
  have key_succ_le : key.val + 1 ≤ n := by
    omega
  obtain ⟨rawLeft, leftHeight⟩ :=
    exists_logHeightTree 0 leftSize
  let left : BST 0 key.val :=
    castUpper (by simp [leftSize]) rawLeft
  obtain ⟨rawRight, rightHeight⟩ :=
    exists_logHeightTree (key.val + 1) rightSize
  have rightUpper :
      key.val + 1 + rightSize = n := by
    dsimp [rightSize]
    omega
  let right : BST (key.val + 1) n :=
    castUpper rightUpper rawRight
  let tree : BST 0 n := .node left right
  have leftSize_le : leftSize + 1 ≤ n + 1 := by
    dsimp [leftSize]
    omega
  have rightSize_le : rightSize + 1 ≤ n + 1 := by
    dsimp [rightSize]
    omega
  have leftBound :
      left.height ≤ Nat.clog 2 (n + 1) := by
    rw [show left.height = rawLeft.height by
      simp [left]]
    exact leftHeight.trans
      (Nat.clog_mono_right 2 leftSize_le)
  have rightBound :
      right.height ≤ Nat.clog 2 (n + 1) := by
    rw [show right.height = rawRight.height by
      simp [right]]
    exact rightHeight.trans
      (Nat.clog_mono_right 2 rightSize_le)
  refine ⟨tree, ⟨left, right, rfl⟩, ?_⟩
  simp only [tree, Splay.Tree.BST.height]
  exact Nat.add_le_add_right (max_le leftBound rightBound) 1

/-- A chosen logarithmic-height tree rooted at the supplied key. -/
noncomputable def rootedBalancedTree
    {n : ℕ} (key : Fin n) : BST 0 n := by
  classical
  exact Classical.choose (exists_rootedLogHeightTree key)

theorem rootedBalancedTree_hasRoot
    {n : ℕ} (key : Fin n) :
    (rootedBalancedTree key).HasRoot key.val := by
  classical
  exact
    (Classical.choose_spec
      (exists_rootedLogHeightTree key)).1

theorem rootedBalancedTree_height_le
    {n : ℕ} (key : Fin n) :
    (rootedBalancedTree key).height ≤
      Nat.clog 2 (n + 1) + 1 := by
  classical
  exact
    (Classical.choose_spec
      (exists_rootedLogHeightTree key)).2

/-- Universal constants sufficient for stationary request sequences. -/
def stationaryBounds : Bounds where
  heightMultiplier := 3
  maxRotationDepth := 0
  costMultiplier := 1
  heightMultiplier_pos := by omega
  costMultiplier_pos := by omega

/-- Every key in a stationary sequence equals its fixed root key. -/
def IsStationary {n : ℕ}
    (key : Fin n) (accesses : List (Fin n)) : Prop :=
  ∀ request ∈ accesses, request = key

/-- A stationary sequence is served in a single balanced state. -/
noncomputable def stationaryTrace
    {n : ℕ} (key : Fin n) (accesses : List (Fin n))
    (stationary : IsStationary key accesses) :
    ComparisonTrace n accesses where
  rotationCount := 0
  state := fun _ => rootedBalancedTree key
  rotationDepth := Fin.elim0
  rotates := fun step => Fin.elim0 step
  servedAt := fun _ => 0
  servedInOrder := fun _ _ _ => le_rfl
  serves := by
    intro request
    have member := accesses.get_mem request
    have equal := stationary (accesses.get request) member
    change
      (rootedBalancedTree key).HasRoot
        (accesses.get request).val
    rw [equal]
    exact rootedBalancedTree_hasRoot key

/-- The stationary trace satisfies uniform normal form. -/
theorem stationaryTrace_normal
    {n : ℕ} (key : Fin n) (accesses : List (Fin n))
    (stationary : IsStationary key accesses) :
    IsNormal stationaryBounds
      (stationaryTrace key accesses stationary) := by
  constructor
  · intro time
    change (rootedBalancedTree key).height ≤
      3 * Analysis.stabilizedLog n
    have base :=
      (rootedBalancedTree_height_le key).trans
        (Nat.add_le_add_right
          (clog_succ_le_two_stabilizedLog n) 1)
    have log_pos := Analysis.stabilizedLog_pos n
    omega
  · intro step
    exact Fin.elim0 step

/-- A stationary sequence has offline optimum exactly its request count. -/
theorem offlineOptCost_eq_length_of_stationary
    {n : ℕ} (key : Fin n) (accesses : List (Fin n))
    (stationary : IsStationary key accesses) :
    OfflineOptimum.offlineOptCost accesses = accesses.length := by
  let tree := rootedBalancedTree key
  have allRooted :
      ∀ request ∈ accesses, tree.HasRoot request.val := by
    intro request member
    have equal := stationary request member
    simpa [tree, equal] using rootedBalancedTree_hasRoot key
  have execution :
      OfflineOptimum.Execution accesses tree tree 0 :=
    OfflineOptimum.Execution.ofAllRooted tree allRooted
  have upper :=
    OfflineOptimum.offlineOptCost_le_ofExecution execution
  have lower :=
    OfflineOptimum.requests_le_offlineOptCost accesses
  omega

/-- Stationary request sequences satisfy the optimal normal-form bound. -/
theorem exists_normalOptimalTrace_of_stationary
    {n : ℕ} (key : Fin n) (accesses : List (Fin n))
    (stationary : IsStationary key accesses) :
    ∃ trace : ComparisonTrace n accesses,
      IsNormal stationaryBounds trace ∧
        trace.cost ≤
          stationaryBounds.costMultiplier *
            OfflineOptimum.offlineOptCost accesses := by
  refine
    ⟨stationaryTrace key accesses stationary,
      stationaryTrace_normal key accesses stationary, ?_⟩
  rw [offlineOptCost_eq_length_of_stationary
    key accesses stationary]
  simp [ComparisonTrace.cost, stationaryTrace,
    stationaryBounds]

/--
Every contextual rotation lies strictly above two actual keys in the tree.
This elementary size bound controls rotation depth on bounded universes.
-/
theorem rotationDepth_add_two_le_size
    {depth lower upper : ℕ}
    {before after : BST lower upper}
    (rotation : RotationAt depth before after) :
    depth + 2 ≤ before.size := by
  induction rotation with
  | root rootRotation =>
      cases rootRotation <;>
        simp only [Splay.Tree.BST.size] <;> omega
  | leftContext rotation right ih =>
      simp only [Splay.Tree.BST.size]
      omega
  | rightContext left rotation ih =>
      simp only [Splay.Tree.BST.size]
      omega

/-- Normal-form constants sufficient on universes of at most `limit` keys. -/
def finiteUniverseBounds (limit : ℕ) (positive : 0 < limit) : Bounds where
  heightMultiplier := limit
  maxRotationDepth := limit
  costMultiplier := 1
  heightMultiplier_pos := positive
  costMultiplier_pos := by omega

/-- Normal form restricted to nonempty key universes of size at most `limit`. -/
def HypothesisUpTo (model : CostModel) (limit : ℕ) : Prop :=
  ∃ bounds : Bounds,
    ∀ (n : ℕ), 0 < n → n ≤ limit →
      ∀ accesses : List (Fin n),
        ∃ trace : ComparisonTrace n accesses,
          IsNormal bounds trace ∧
            trace.cost ≤
              bounds.costMultiplier * model.optCost accesses

/--
On every fixed finite range of universe sizes, the optimal trace itself is
already a normal-form trace.  The constants depend on the range bound; this
pinpoints that the unresolved theorem is precisely uniformity as `n` grows.
-/
theorem exists_normalOptimalTrace_of_le
    (limit : ℕ) (positive : 0 < limit)
    {n : ℕ} (_n_pos : 0 < n) (n_le : n ≤ limit)
    (accesses : List (Fin n)) :
    ∃ trace : ComparisonTrace n accesses,
      IsNormal (finiteUniverseBounds limit positive) trace ∧
        trace.cost ≤
          (finiteUniverseBounds limit positive).costMultiplier *
            OfflineOptimum.offlineOptCost accesses := by
  obtain ⟨trace, cost_eq⟩ :=
    exists_optimalComparisonTrace accesses
  refine ⟨trace, ?_, ?_⟩
  · constructor
    · intro time
      calc
        (trace.state time).height ≤ (trace.state time).size :=
          (trace.state time).height_le_size
        _ = n := (trace.state time).size_eq_upper
        _ ≤ limit := n_le
        _ ≤ limit * Analysis.stabilizedLog n := by
          have log_pos := Analysis.stabilizedLog_pos n
          exact Nat.le_mul_of_pos_right limit log_pos
    · intro step
      have depthSize :=
        rotationDepth_add_two_le_size (trace.rotates step)
      have size_eq : (trace.state step.castSucc).size = n :=
        (trace.state step.castSucc).size_eq_upper
      change trace.rotationDepth step ≤ limit
      omega
  · simp only [finiteUniverseBounds]
    simp [cost_eq]

/--
Consequently, normal form for the genuine offline optimum is completely
proved on every fixed finite range of key-universe sizes.
-/
theorem hypothesisUpTo_concreteOfflineCostModel
    (limit : ℕ) (positive : 0 < limit) :
    HypothesisUpTo OfflineOptimum.concreteOfflineCostModel limit := by
  refine ⟨finiteUniverseBounds limit positive, ?_⟩
  intro n n_pos n_le accesses
  simpa using
    exists_normalOptimalTrace_of_le
      limit positive n_pos n_le accesses

/--
The exact remaining manuscript input: a uniform constant-factor conversion
of any comparison trace to bounded-height, bounded-depth normal form.
-/
def UniformTraceNormalizer : Prop :=
  ∃ bounds : Bounds,
    ∀ (n : ℕ), 0 < n →
      ∀ (accesses : List (Fin n))
        (source : ComparisonTrace n accesses),
        ∃ target : ComparisonTrace n accesses,
          IsNormal bounds target ∧
            target.cost ≤ bounds.costMultiplier * source.cost

/--
The minimal uniform statement needed at the optimum.  Unlike
`UniformTraceNormalizer`, it asks for normalization only when the supplied
source trace actually attains `offlineOptCost`.
-/
def UniformOptimalTraceNormalizer : Prop :=
  ∃ bounds : Bounds,
    ∀ (n : ℕ), 0 < n →
      ∀ (accesses : List (Fin n))
        (source : ComparisonTrace n accesses),
        source.cost = OfflineOptimum.offlineOptCost accesses →
          ∃ target : ComparisonTrace n accesses,
            IsNormal bounds target ∧
              target.cost ≤ bounds.costMultiplier * source.cost

/--
A uniform trace normalizer immediately discharges the repository's
`NormalForm.Hypothesis` for the concrete offline optimum.
-/
theorem hypothesis_of_uniformTraceNormalizer
    (normalizer : UniformTraceNormalizer) :
    Splay.Assumptions.NormalForm.Hypothesis
      OfflineOptimum.concreteOfflineCostModel := by
  obtain ⟨bounds, normalize⟩ := normalizer
  refine ⟨bounds, ?_⟩
  intro n n_pos accesses
  obtain ⟨source, sourceCost⟩ :=
    exists_optimalComparisonTrace accesses
  obtain ⟨target, normal, targetCost⟩ :=
    normalize n n_pos accesses source
  refine ⟨target, normal, ?_⟩
  rw [OfflineOptimum.concreteOfflineCostModel_optCost]
  simpa [sourceCost] using targetCost

/--
The optimal-source normalizer is exactly equivalent to the remaining
repository hypothesis.  Thus this is a kernel-checked characterization of the
last normal-form boundary, rather than merely a stronger sufficient axiom.
-/
theorem uniformOptimalTraceNormalizer_iff_hypothesis :
    UniformOptimalTraceNormalizer ↔
      Splay.Assumptions.NormalForm.Hypothesis
        OfflineOptimum.concreteOfflineCostModel := by
  constructor
  · rintro ⟨bounds, normalize⟩
    refine ⟨bounds, ?_⟩
    intro n n_pos accesses
    obtain ⟨source, sourceCost⟩ :=
      exists_optimalComparisonTrace accesses
    obtain ⟨target, normal, targetCost⟩ :=
      normalize n n_pos accesses source sourceCost
    refine ⟨target, normal, ?_⟩
    rw [OfflineOptimum.concreteOfflineCostModel_optCost]
    simpa [sourceCost] using targetCost
  · rintro ⟨bounds, realize⟩
    refine ⟨bounds, ?_⟩
    intro n n_pos accesses source sourceCost
    obtain ⟨target, normal, targetCost⟩ :=
      realize n n_pos accesses
    refine ⟨target, normal, ?_⟩
    rw [OfflineOptimum.concreteOfflineCostModel_optCost] at targetCost
    simpa [sourceCost] using targetCost

end Splay.Accounting.OfflineNormalForm
