import FreshPortRestoration

/-!
Every actual intermediate paid-restoration state and its immutable reader
snapshot. This is the temporal interface for expanding one comparator macro
into one pre-restoration batch step and one state transition per paid port.
-/
namespace GreedyMerge.HeapAllocation

open OrderedBlocks Primitives
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

noncomputable def restorationState {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry) :
    List (External n) → ℕ → ℕ → HeapSides n → ℕ → HeapSides n
  | [], _, _, states, _ => states
  | _::_, _, _, states, 0 => states
  | record::rest, stage, start, states, index+1 =>
      let names := portNames snapshot tree record start states
      let head := restorePort snapshot tree names (reader stage states record) record states
      restorationState snapshot tree reader rest (stage+1) (restoreNext snapshot tree record start states) head.1 index

@[simp] theorem restorationState_zero {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n) :
    restorationState snapshot tree reader ports stage start states 0=states := by
  cases ports <;> rfl

theorem restorationState_final {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n) :
    restorationState snapshot tree reader ports stage start states ports.length =
      (freshRestorePorts snapshot tree reader ports stage start states).states := by
  induction ports generalizing stage start states with
  | nil => rfl
  | cons record rest ih => exact ih (stage+1) _ _

/-- Every executed factory entry reads exactly the actual pre-insertion
state, at the same stage used in the immutable joined timestamp. -/
theorem freshRestorePorts_reader_at {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n)
    (index : ℕ) (inside : index<ports.length) (record owner : External n) :
    (freshRestorePorts snapshot tree reader ports stage start states).makeEntry (stage+index) record owner =
      reader (stage+index) (restorationState snapshot tree reader ports stage start states index) record owner := by
  induction ports generalizing stage start states index with
  | nil => simp at inside
  | cons port rest ih =>
      cases index with
      | zero => simp [freshRestorePorts,restorationState]
      | succ index =>
          have tail := ih (stage+1) (restoreNext snapshot tree port start states)
            (restorePort snapshot tree (portNames snapshot tree port start states) (reader stage states port) port states).1
            index (by simpa using inside)
          simpa only [freshRestorePorts,restorationState,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
            show ¬stage+(index+1)=stage by omega,if_false] using tail

/-- Exact one-step relation with the returned names and factory from the
original full execution, not freshly chosen parameters at the tail. -/
theorem freshRestorePorts_step {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n)
    (index : ℕ) (inside : index<ports.length) :
    let result := freshRestorePorts snapshot tree reader ports stage start states
    let record := ports[index]
    (restorePort snapshot tree (result.names (stage+index)) (result.makeEntry (stage+index) record) record
      (restorationState snapshot tree reader ports stage start states index)).1 =
        restorationState snapshot tree reader ports stage start states (index+1) := by
  induction ports generalizing stage start states index with
  | nil => simp at inside
  | cons port rest ih =>
      cases index with
      | zero => simp [freshRestorePorts,restorationState]
      | succ index =>
          have tail := ih (stage+1) (restoreNext snapshot tree port start states)
            (restorePort snapshot tree (portNames snapshot tree port start states) (reader stage states port) port states).1
            index (by simpa using inside)
          simpa only [freshRestorePorts,restorationState,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
            show ¬stage+(index+1)=stage by omega,if_false] using tail

#print axioms restorationState_final
#print axioms freshRestorePorts_reader_at
#print axioms freshRestorePorts_step

end GreedyMerge.HeapAllocation
