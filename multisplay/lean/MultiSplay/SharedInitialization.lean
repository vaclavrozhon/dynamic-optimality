import MultiSplay.SharedSplayComponents
import Splay.Lazy.CanonicalInitializationCost

/-!
# One-time initialization of the shared component histories

A setup step executes the existing canonical initializer in a passive frame.
Its value changes are virtual accounting operations: their number may depend
on G, but the initialization mass counts only the component's external slots.
-/

namespace MultiSplay

open Splay.Interface

theorem InterfaceFramedTrace.Framed.blocks_length {n m : Nat} {params : Parameters}
    {component : State n} {whole : State m} (framed : InterfaceFramedTrace.Framed params component whole) :
    whole.blocks.length = framed.frame.blocks.length + component.blocks.length := by
  have count := framed.equivalent.1.length_eq
  simpa only [List.length_map, InterfacePrefix.state, List.length_append] using count.symm

namespace SharedSplay

open Splay.Rank (Snapshot)
open Splay.Lazy.Canonical

variable {m : Nat} {params : Parameters}

structure Setup {n : Nat} (snapshot : Snapshot n) (tree : Splay.Tree.BST 0 n)
    (params : Parameters) (whole : State m)
    (initial : InterfaceFramedTrace.Framed params (emptyCanonicalState snapshot tree).toInterface whole) where
  final : State m
  operations : List (Operation m)
  trace : Trace params whole operations final
  framed : InterfaceFramedTrace.Framed params (canonicalState snapshot tree).toInterface final
  element_eq : framed.element = initial.element
  frame_eq : framed.frame = initial.frame
  inserts_eq : totalInserts operations = totalInserts (Splay.Lazy.eraseOperations (canonicalInitializationEvents snapshot tree))
  increases_eq : totalIncreases operations = totalIncreases (Splay.Lazy.eraseOperations (canonicalInitializationEvents snapshot tree))
  activity_eq : totalActivity operations = 0

theorem setup_exists {n : Nat} (snapshot : Snapshot n) (tree : Splay.Tree.BST 0 n)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound : Splay.Analysis.contractedGap snapshot.maxRank ≤ params.valueBound)
    (whole : State m) (initial : InterfaceFramedTrace.Framed params (emptyCanonicalState snapshot tree).toInterface whole) :
    Nonempty (Setup snapshot tree params whole initial) := by
  have execution := (emptyCanonicalState_canonicalState_trace snapshot tree params growingLimit valueBound).toInterface
  obtain ⟨word, final, actual, ⟨next, elementEq, frameEq⟩, _, activity, inserts, increases, _⟩ := initial.trace execution
  exact ⟨⟨final, word, actual, next, elementEq, frameEq, inserts, increases,
    activity.trans (canonicalInitializationEvents_activity snapshot tree)⟩⟩

namespace Setup

variable {n : Nat} {snapshot : Snapshot n} {tree : Splay.Tree.BST 0 n} {whole : State m}
  {initial : InterfaceFramedTrace.Framed params (emptyCanonicalState snapshot tree).toInterface whole}
  (setup : Setup snapshot tree params whole initial)

theorem inserts : totalInserts setup.operations ≤ 2*n+1 := by
  rw [setup.inserts_eq]
  exact canonicalInitializationEvents_inserts snapshot tree

theorem increases (valueBound : Splay.Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    totalIncreases setup.operations ≤ 3 * params.valueBound * (2*n+1) := by
  rw [setup.increases_eq]
  exact canonicalInitializationEvents_increases snapshot tree params valueBound

theorem growth : totalBlockGrowth setup.operations = 2 * (2*n+1) := by
  have counted := setup.trace.blocks_length_eq
  have before := initial.blocks_length
  have after := setup.framed.blocks_length
  rw [setup.frame_eq] at after
  simp only [Splay.Lazy.State.toInterface, List.length_map, emptyCanonicalState_blocks,
    List.length_nil, Nat.add_zero] at before
  simp only [Splay.Lazy.State.toInterface, List.length_map, canonicalState_blocks_length] at after
  omega

end Setup

/-- Each setup uses a current passive frame. Previously initialized components
and their immutable creator records are retained by the same strict trace. -/
inductive Initialization (params : Parameters) : State m → State m → Type
  | done (state : State m) : Initialization params state state
  | next {n : Nat} {snapshot : Snapshot n} {tree : Splay.Tree.BST 0 n} {first middle last : State m}
      {initial : InterfaceFramedTrace.Framed params (emptyCanonicalState snapshot tree).toInterface first}
      (setup : Setup snapshot tree params first initial)
      (valueBound : Splay.Analysis.contractedGap snapshot.maxRank ≤ params.valueBound)
      (final_eq : setup.final = middle)
      (tail : Initialization params middle last) : Initialization params first last

namespace Initialization

variable {first last : State m}

def operations : {first last : State m} → Initialization params first last → List (Operation m)
  | _, _, .done _ => []
  | _, _, .next setup _ _ tail => setup.operations ++ tail.operations

def mass : {first last : State m} → Initialization params first last → Nat
  | _, _, .done _ => 0
  | _, _, .next (n := n) _ _ _ tail => (2*n+1) + tail.mass

theorem trace (initialization : Initialization params first last) (valid : first.Valid params) :
    Trace params first initialization.operations last := by
  induction initialization with
  | done state => exact .nil valid
  | next setup valueBound same tail ih =>
      have head : Trace params _ setup.operations _ := same ▸ setup.trace
      exact InterfaceForest.trace_append head (ih (InterfaceForest.trace_final_valid head))

theorem activity (initialization : Initialization params first last) : totalActivity initialization.operations = 0 := by
  induction initialization with
  | done state => rfl
  | next setup valueBound same tail ih => simp [operations, totalActivity_append, setup.activity_eq, ih]

theorem inserts (initialization : Initialization params first last) : totalInserts initialization.operations ≤ initialization.mass := by
  induction initialization with
  | done state => exact Nat.le_refl 0
  | next setup valueBound same tail ih =>
      have paid := setup.inserts
      simp only [operations, totalInserts_append, mass]
      omega

theorem increases (initialization : Initialization params first last) :
    totalIncreases initialization.operations ≤ 3 * params.valueBound * initialization.mass := by
  induction initialization with
  | done state => simp [operations, totalIncreases, mass]
  | next setup valueBound same tail ih =>
      have paid := setup.increases valueBound
      simp only [operations, totalIncreases_append, mass]
      nlinarith

theorem growth (initialization : Initialization params first last) : totalBlockGrowth initialization.operations = 2 * initialization.mass := by
  induction initialization with
  | done state => rfl
  | next setup valueBound same tail ih =>
      have appendGrowth : totalBlockGrowth (setup.operations ++ tail.operations) = totalBlockGrowth setup.operations + totalBlockGrowth tail.operations := by
        simp [totalBlockGrowth]
      simp only [operations, mass, appendGrowth, setup.growth, ih]
      omega

theorem boundary_credit (initialization : Initialization params first last) (initialized : first.Initial params) (cutoff : Nat) :
    boundaryCredit cutoff last ≤ boundaryCreditCapacity cutoff * (2 * initialization.mass) := by
  have paid := (initialization.trace initialized.1).boundaryCredit_bound (cutoff := cutoff)
  simpa only [initialization.growth, boundaryCredit, initialized.2, List.map_nil, List.sum_nil, Nat.zero_add] using paid

end Initialization
end SharedSplay
end MultiSplay
