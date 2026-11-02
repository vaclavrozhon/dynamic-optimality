import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega

/-!
# Turn accounting for cyclic micro/macro words

This module proves general identities for direction words.  A Boolean direction
records whether an edge in an ordered word goes left or right; a turn is a
change of direction.  The identities apply to arbitrary finite words, rather
than to bounded enumerations of instances.

The bridge from concrete primary-reference access words to the direction/run
representation in this file is a separate obligation.  In particular, none of
the theorems here asserts the dynamic BST lower bound by itself.
-/

namespace ChaCha.TurnAccounting

/-- One turn between two consecutive nonzero directions. -/
def turn (a b : Bool) : ℕ := if a = b then 0 else 1

/-- Direction changes along a path whose incoming direction is `incoming`. -/
def changesFrom : Bool → List Bool → ℕ
  | _, [] => 0
  | incoming, d :: ds => turn incoming d + changesFrom d ds

/-- Direction changes internal to a linear direction word. -/
def linearTurns : List Bool → ℕ
  | [] => 0
  | d :: ds => changesFrom d ds

/-- Turns in a cyclic direction word. Empty and one-letter words have no turns. -/
def cyclicTurns (ds : List Bool) : ℕ :=
  changesFrom (ds.getLastD false) ds

@[simp] theorem turn_self (a : Bool) : turn a a = 0 := by simp [turn]

@[simp] theorem changesFrom_nil (a : Bool) : changesFrom a [] = 0 := rfl

theorem getLastD_append (xs ys : List Bool) (fallback : Bool) :
    (xs ++ ys).getLastD fallback = ys.getLastD (xs.getLastD fallback) := by
  induction xs generalizing fallback with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.getLastD_cons]
    exact ih x

theorem changesFrom_append (incoming : Bool) (xs ys : List Bool) :
    changesFrom incoming (xs ++ ys) =
      changesFrom incoming xs + changesFrom (xs.getLastD incoming) ys := by
  induction xs generalizing incoming with
  | nil => simp [changesFrom]
  | cons x xs ih =>
    simp only [List.cons_append, changesFrom, List.getLastD_cons]
    rw [ih]
    omega

theorem changesFrom_nonempty (incoming d : Bool) (ds : List Bool) :
    changesFrom incoming (d :: ds) = turn incoming d + linearTurns (d :: ds) := rfl

/-- Only turns at joins of blocks; empty blocks do not create joins. -/
def joinsFrom : Bool → List (List Bool) → ℕ
  | _, [] => 0
  | incoming, [] :: blocks => joinsFrom incoming blocks
  | incoming, (d :: ds) :: blocks =>
      turn incoming d + joinsFrom (ds.getLastD d) blocks

/-- Cyclic joins, including the join of the last nonempty block to the first. -/
def cyclicJoins (blocks : List (List Bool)) : ℕ :=
  joinsFrom (blocks.flatten.getLastD false) blocks

theorem changesFrom_flatten (incoming : Bool) (blocks : List (List Bool)) :
    changesFrom incoming blocks.flatten =
      (blocks.map linearTurns).sum + joinsFrom incoming blocks := by
  induction blocks generalizing incoming with
  | nil => simp [joinsFrom]
  | cons block blocks ih =>
    cases block with
    | nil => simpa [joinsFrom, linearTurns] using ih incoming
    | cons d ds =>
      simp only [List.flatten_cons, List.map_cons, List.sum_cons]
      rw [changesFrom_append, ih]
      simp only [changesFrom, linearTurns, joinsFrom, List.getLastD_cons]
      omega

/-- Exact cyclic block-gluing identity, with no hypotheses on block sizes. -/
theorem cyclicTurns_flatten (blocks : List (List Bool)) :
    cyclicTurns blocks.flatten =
      (blocks.map linearTurns).sum + cyclicJoins blocks := by
  exact changesFrom_flatten _ _

/-- A coarse run is represented by its internal micro directions and its outgoing
macro direction. Empty `micro` means that the run is fine-homogeneous. -/
structure Run where
  micro : List Bool
  exit : Bool
  deriving DecidableEq

def Run.parentBlock (r : Run) : List Bool := r.micro ++ [r.exit]

def Run.entryTurn (incoming : Bool) (r : Run) : ℕ :=
  match r.micro with
  | [] => 0
  | d :: _ => turn incoming d

def Run.exitTurn (r : Run) : ℕ :=
  match r.micro with
  | [] => 0
  | d :: ds => turn (ds.getLastD d) r.exit

def Run.trivialTurn (incoming : Bool) (r : Run) : ℕ :=
  match r.micro with
  | [] => turn incoming r.exit
  | _ :: _ => 0

def Run.nontrivialMacroTurn (incoming : Bool) (r : Run) : ℕ :=
  match r.micro with
  | [] => 0
  | _ :: _ => turn incoming r.exit

/-- Sum a run-local quantity while threading the actual previous macro direction. -/
def runSum (f : Bool → Run → ℕ) : Bool → List Run → ℕ
  | _, [] => 0
  | incoming, r :: rs => f incoming r + runSum f r.exit rs

def runInternal (rs : List Run) : ℕ := (rs.map fun r => linearTurns r.micro).sum

def cyclicIncoming (rs : List Run) : Bool := (rs.map Run.exit).getLastD false

def entryTurns (rs : List Run) : ℕ := runSum Run.entryTurn (cyclicIncoming rs) rs
def exitTurns (rs : List Run) : ℕ := (rs.map Run.exitTurn).sum
def trivialTurns (rs : List Run) : ℕ := runSum Run.trivialTurn (cyclicIncoming rs) rs
def nontrivialMacroTurns (rs : List Run) : ℕ :=
  runSum Run.nontrivialMacroTurn (cyclicIncoming rs) rs

def parentTurns (rs : List Run) : ℕ := cyclicTurns (rs.map Run.parentBlock).flatten
def macroTurns (rs : List Run) : ℕ := cyclicTurns (rs.map Run.exit)

theorem run_parent_decomposition (incoming : Bool) (r : Run) :
    changesFrom incoming r.parentBlock = linearTurns r.micro +
      r.entryTurn incoming + r.exitTurn + r.trivialTurn incoming := by
  rcases r with ⟨micro, out⟩
  cases micro with
  | nil => simp [Run.parentBlock, changesFrom, linearTurns, Run.entryTurn,
      Run.exitTurn, Run.trivialTurn]
  | cons d ds =>
    simp only [Run.parentBlock, changesFrom_append]
    simp only [changesFrom, linearTurns, Run.entryTurn, Run.exitTurn,
      Run.trivialTurn, List.getLastD_cons]
    omega

theorem parent_decomposition_from (incoming : Bool) (rs : List Run) :
    changesFrom incoming (rs.map Run.parentBlock).flatten =
      runInternal rs + runSum Run.entryTurn incoming rs +
        (rs.map Run.exitTurn).sum + runSum Run.trivialTurn incoming rs := by
  induction rs generalizing incoming with
  | nil => simp [runInternal, runSum]
  | cons r rs ih =>
    simp only [List.map_cons, List.flatten_cons]
    rw [changesFrom_append, run_parent_decomposition]
    have hlast : r.parentBlock.getLastD incoming = r.exit := by
      simp [Run.parentBlock]
    rw [hlast, ih]
    simp only [runInternal, List.map_cons, List.sum_cons, runSum]
    omega

theorem parent_last (rs : List Run) (fallback : Bool) :
    (rs.map Run.parentBlock).flatten.getLastD fallback =
      (rs.map Run.exit).getLastD fallback := by
  induction rs generalizing fallback with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.flatten_cons, getLastD_append, List.getLastD_cons]
    simpa [Run.parentBlock, getLastD_append] using ih r.exit

/-- Counts the actual parent direction list by internal, entry, exit, and trivial
run turns. This is the first counting equation in the manuscript. -/
theorem parent_decomposition (rs : List Run) :
    parentTurns rs = runInternal rs + entryTurns rs + exitTurns rs + trivialTurns rs := by
  unfold parentTurns cyclicTurns
  rw [parent_last]
  exact parent_decomposition_from _ _

theorem macro_decomposition_from (incoming : Bool) (rs : List Run) :
    changesFrom incoming (rs.map Run.exit) =
      runSum Run.trivialTurn incoming rs + runSum Run.nontrivialMacroTurn incoming rs := by
  induction rs generalizing incoming with
  | nil => simp [runSum]
  | cons r rs ih =>
    simp only [List.map_cons, changesFrom, runSum]
    rw [ih]
    cases h : r.micro <;>
      simp only [Run.trivialTurn, Run.nontrivialMacroTurn, h] <;> omega

/-- The macro turns split according to whether the corresponding run is trivial. -/
theorem macro_decomposition (rs : List Run) :
    macroTurns rs = trivialTurns rs + nontrivialMacroTurns rs := by
  exact macro_decomposition_from _ _

/-- Each group contains the micro direction blocks belonging to one coarse cell,
in their cyclic visitation order. The `Perm` hypothesis below specifies that
every coarse run is present once, including any empty micro blocks. -/
def microTurns (groups : List (List (List Bool))) : ℕ :=
  (groups.map fun blocks => cyclicTurns blocks.flatten).sum

def joinTurns (groups : List (List (List Bool))) : ℕ :=
  (groups.map cyclicJoins).sum

theorem micro_decomposition_raw (groups : List (List (List Bool))) :
    microTurns groups = (groups.flatten.map linearTurns).sum + joinTurns groups := by
  induction groups with
  | nil => simp [microTurns, joinTurns]
  | cons blocks groups ih =>
    simp only [microTurns, joinTurns, List.map_cons, List.sum_cons] at ih ⊢
    rw [cyclicTurns_flatten, ih]
    simp only [List.flatten_cons, List.map_append, List.sum_append]
    omega

/-- Exact micro-word count, proved from the concrete block-gluing identity. -/
theorem micro_decomposition (rs : List Run) (groups : List (List (List Bool)))
    (partition : groups.flatten.Perm (rs.map Run.micro)) :
    microTurns groups = runInternal rs + joinTurns groups := by
  rw [micro_decomposition_raw]
  have h := (partition.map linearTurns).sum_eq
  simpa [runInternal, List.map_map, Function.comp_def] using congrArg (fun k => k + joinTurns groups) h

/-- The local turn identity, in subtraction-free form over natural numbers.

All counts are defined from concrete direction lists. The only structural
hypothesis is that the grouped micro blocks partition the parent runs. Applying
this to access words additionally requires proving the normalized return rule,
which ensures that no extra micro direction appears between successive runs.
-/
theorem local_turn_identity (rs : List Run) (groups : List (List (List Bool)))
    (partition : groups.flatten.Perm (rs.map Run.micro)) :
    joinTurns groups + parentTurns rs + nontrivialMacroTurns rs =
      macroTurns rs + microTurns groups + entryTurns rs + exitTurns rs := by
  have hp := parent_decomposition rs
  have hm := macro_decomposition rs
  have hμ := micro_decomposition rs groups partition
  omega

/-- A gap between two successive nontrivial runs in one coarse cell.
`outsideSides` records on which side of that cell the outside queries lie.
The last and next micro directions are the directions adjoining its join. -/
structure Gap where
  previousMicro : Bool
  nextMicro : Bool
  outsideSides : List Bool
  deriving DecidableEq

/-- Whether the retained record encounters an outside query on the opposite side. -/
def Gap.delayed (g : Gap) : ℕ :=
  if g.outsideSides.any (fun side => side != g.previousMicro) then 1 else 0

/-- The direction entering the next run is opposite the side of its last outside query. -/
def Gap.entry (g : Gap) : ℕ :=
  turn (!g.outsideSides.getLastD g.previousMicro) g.nextMicro

def Gap.join (g : Gap) : ℕ := turn g.previousMicro g.nextMicro

theorem getLastD_eq_of_no_opposite (directions : List Bool) (d : Bool)
    (h : directions.any (fun side => side != d) = false) :
    directions.getLastD d = d := by
  induction directions with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
    obtain ⟨rfl, hx⟩ := h
    simpa only [List.getLastD_cons] using ih hx

/-- The gap trichotomy: a delayed reversal, an entry turn, or a micro join turn
always pays. The statement even holds for an empty formal excursion, although
gaps arising from distinct coarse runs always have a nonempty excursion. -/
theorem gap_cover (g : Gap) : 1 ≤ g.delayed + g.entry + g.join := by
  by_cases h : g.outsideSides.any (fun side => side != g.previousMicro) = true
  · simp only [Gap.delayed, h, ↓reduceIte]
    omega
  · have hf : g.outsideSides.any (fun side => side != g.previousMicro) = false :=
      Bool.eq_false_iff.mpr h
    have hl := getLastD_eq_of_no_opposite g.outsideSides g.previousMicro hf
    simp only [Gap.delayed, hf, Bool.false_eq_true, ↓reduceIte, Gap.entry, hl, Gap.join]
    cases g.previousMicro <;> cases g.nextMicro <;> decide

/-- Summing gap coverage counts occurrences, so repeated coarse-cell names or
directions cause no identification of distinct demands. -/
theorem gaps_cover (gaps : List Gap) :
    gaps.length ≤ (gaps.map Gap.delayed).sum +
      (gaps.map Gap.entry).sum + (gaps.map Gap.join).sum := by
  induction gaps with
  | nil => simp
  | cons g gs ih =>
    have hg := gap_cover g
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- Combine the proved turn identity with a concrete gap assignment. The three
inequalities are the remaining occurrence-injection obligations when a caller
constructs gaps from a reference access word. They are not BST hypotheses. -/
theorem local_demand_bound (rs : List Run) (groups : List (List (List Bool)))
    (partition : groups.flatten.Perm (rs.map Run.micro)) (gaps : List Gap)
    (entry_injection : (gaps.map Gap.entry).sum ≤ entryTurns rs)
    (join_injection : (gaps.map Gap.join).sum ≤ joinTurns groups) :
    gaps.length + parentTurns rs ≤ macroTurns rs + microTurns groups +
      (gaps.map Gap.delayed).sum + 2 * entryTurns rs + exitTurns rs := by
  have hg := gaps_cover gaps
  have ht := local_turn_identity rs groups partition
  omega

section Hierarchy

variable {Node : Type*} [Fintype Node] [DecidableEq Node]

/-- Sum the child potentials using an explicit parent map. The root is not its
own child, regardless of the otherwise irrelevant value of `parent root`. -/
def childPotential (root : Node) (parent : Node → Node) (v : Node → ℤ) (q : Node) : ℤ :=
  ∑ c : Node, if c ≠ root ∧ parent c = q then v c else 0

/-- Every nonroot potential occurs exactly once among all child sums. No
acyclicity assumption is needed for this counting fact. -/
theorem sum_childPotential (root : Node) (parent : Node → Node) (v : Node → ℤ) :
    ∑ q : Node, childPotential root parent v q =
      (∑ c : Node, v c) - v root := by
  unfold childPotential
  rw [Finset.sum_comm]
  have h : (∑ c : Node, ∑ q : Node,
      if c ≠ root ∧ parent c = q then v c else 0) =
      ∑ c : Node, if c = root then 0 else v c := by
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : c = root
    · simp [hc]
    · simp [hc, eq_comm]
  rw [h]
  have hsplit : (∑ c : Node, if c = root then 0 else v c) + v root =
      ∑ c : Node, v c := by
    calc
      _ = (∑ c : Node, if c = root then 0 else v c) +
          ∑ c : Node, if c = root then v c else 0 := by simp
      _ = ∑ c : Node, ((if c = root then 0 else v c) +
          if c = root then v c else 0) := by rw [Finset.sum_add_distrib]
      _ = ∑ c : Node, v c := by
        apply Finset.sum_congr rfl
        intro c _
        split_ifs <;> simp
  omega

/-- Exact telescoping over any finite parent hierarchy. `internal` may contain
additional childless nodes, but every genuine parent must be internal. At a
leaf the parent-minus-child potential is left as a boundary contribution. -/
theorem hierarchy_telescope (root : Node) (parent : Node → Node)
    (internal : Node → Prop) [DecidablePred internal] (v : Node → ℤ)
    (parent_internal : ∀ c, c ≠ root → internal (parent c)) :
    (∑ q : Node, if internal q then childPotential root parent v q - v q else 0) =
      (∑ q : Node, if internal q then 0 else v q) - v root := by
  have hchild (q : Node) :
      (if internal q then childPotential root parent v q else 0) =
        childPotential root parent v q := by
    by_cases hi : internal q
    · simp [hi]
    · simp only [hi, ↓reduceIte]
      symm
      unfold childPotential
      apply Finset.sum_eq_zero
      intro c _
      split_ifs with h
      · exact False.elim (hi (h.2 ▸ parent_internal c h.1))
      · rfl
  have hpoint (q : Node) :
      (if internal q then childPotential root parent v q - v q else 0) =
        childPotential root parent v q - v q + (if internal q then 0 else v q) := by
    by_cases hi : internal q
    · simp [hi]
    · have hc := hchild q
      simp only [hi, ↓reduceIte] at hc ⊢
      omega
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_childPotential]
  omega

/-- The nonnegative root potential may be dropped after telescoping. -/
theorem hierarchy_telescope_le (root : Node) (parent : Node → Node)
    (internal : Node → Prop) [DecidablePred internal] (v : Node → ℤ)
    (parent_internal : ∀ c, c ≠ root → internal (parent c)) (root_nonneg : 0 ≤ v root) :
    (∑ q : Node, if internal q then childPotential root parent v q - v q else 0) ≤
      ∑ q : Node, if internal q then 0 else v q := by
  rw [hierarchy_telescope root parent internal v parent_internal]
  omega

end Hierarchy

end ChaCha.TurnAccounting
