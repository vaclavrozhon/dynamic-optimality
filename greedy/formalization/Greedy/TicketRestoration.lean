import Greedy.TicketBatches

/-! Paid entry annotations use the actual singleton family and immutable join. -/

namespace Greedy.TicketJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation
open WinnerCredit

abbrev State (n : ℕ) := WinnerCredit.State (External n) MembershipPointer.Ticket
abbrev Action (n : ℕ) := WinnerCredit.Action (External n) MembershipPointer.Ticket

noncomputable def one {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n) (states : States n) : List (Action n) :=
  match canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => []
  | some owner => .entry record owner .ordinary (names.paidFamily, (makeEntry owner).joined) ::
      WinnerCredit.batch (RestorationJournal.labels comparator K (restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1)

theorem one_erases {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n) (states : States n) :
    erase (one comparator tree K names makeEntry record states) =
      RestorationJournal.one comparator tree K names makeEntry record states := by
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record <;>
    simp only [one, RestorationJournal.one, parent, erase, List.flatMap_nil, List.flatMap_cons, eraseOne, List.singleton_append]
  exact congrArg (List.cons _) (batch_erases _)

theorem one_administrative {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n) (states : States n) :
    Administrative (one comparator tree K names makeEntry record states) := by
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => simp [one, parent, Administrative]
  | some owner =>
      intro action member
      simp only [one, parent] at member
      rcases List.mem_cons.mp member with fresh | old
      · subst action; rfl
      · exact batch_administrative _ action old

theorem one_pointer {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n) (states : States n)
    (state : State n) (synced : MembershipPointer.Synced state.ticket states)
    (absent : ¬ GreedyMerge.BlockCoverage.Represented states record.val)
    (keys : ∀ owner, (makeEntry owner).key = record.val) :
    MembershipPointer.Synced (WinnerCredit.run state (one comparator tree K names makeEntry record states)).ticket
      (restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1 := by
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => simpa only [one, restorePort, parent, WinnerCredit.run] using synced
  | some owner =>
      rw [one, parent, WinnerCredit.run, batch_ticket]
      exact MembershipPointer.restore (Snapshot.ofTree comparator) tree names makeEntry record owner parent
        states state.ticket synced absent keys

noncomputable def program {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → States n → External n → External n → Entry) :
    List (External n) → ℕ → ℕ → States n → List (Action n)
  | [], _, _, _ => []
  | record :: rest, stage, start, states =>
      let names := portNames (Snapshot.ofTree comparator) tree record start states
      let head := restorePort (Snapshot.ofTree comparator) tree names (reader stage states record) record states
      one comparator tree K names (reader stage states record) record states ++
        program comparator tree K reader rest (stage+1)
          (restoreNext (Snapshot.ofTree comparator) tree record start states) head.1

theorem program_erases {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → States n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : States n) :
    erase (program comparator tree K reader ports stage start states) =
      RestorationJournal.program comparator tree K reader ports stage start states := by
  induction ports generalizing stage start states with
  | nil => rfl
  | cons record rest ih => rw [program, erase_append, one_erases, ih]; rfl

theorem program_administrative {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → States n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : States n) :
    Administrative (program comparator tree K reader ports stage start states) := by
  induction ports generalizing stage start states with
  | nil => simp [program, Administrative]
  | cons record rest ih => exact (administrative_append ..).mpr ⟨one_administrative comparator tree K _ _ record states, ih (stage+1) _ _⟩

theorem program_pointer {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → States n → External n → External n → Entry)
    (keys : ∀ stage current record owner, (reader stage current record owner).key = record.val)
    (ports : List (External n)) (distinct : ports.Nodup) (stage start : ℕ)
    (states : States n) (ordered : Ordered states)
    (absent : ∀ record ∈ ports, ¬ GreedyMerge.BlockCoverage.Represented states record.val)
    (state : State n) (synced : MembershipPointer.Synced state.ticket states) :
    MembershipPointer.Synced (WinnerCredit.run state (program comparator tree K reader ports stage start states)).ticket
      (freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states).states := by
  induction ports generalizing stage start states state with
  | nil => exact synced
  | cons record rest ih =>
      let names := portNames (Snapshot.ofTree comparator) tree record start states
      let head := restorePort (Snapshot.ofTree comparator) tree names (reader stage states record) record states
      let actions := one comparator tree K names (reader stage states record) record states
      have headSynced := one_pointer comparator tree K names (reader stage states record) record states state synced
        (absent record (by simp)) (keys stage states record)
      have headOrdered := restorePort_valid (Snapshot.ofTree comparator) tree names (reader stage states record)
        record states ordered (keys stage states record) (absent record (by simp))
      have tailAbsent : ∀ other ∈ rest, ¬ GreedyMerge.BlockCoverage.Represented head.1 other.val := by
        intro other member represented
        rcases (restorePort_represented (Snapshot.ofTree comparator) tree names (reader stage states record)
          record states ordered (keys stage states record) other.val).mp represented with previous | ⟨same, _⟩
        · exact absent other (by simp [member]) previous
        · have equal : other = record := Fin.ext same
          exact (List.nodup_cons.mp distinct).1 (equal ▸ member)
      have tail := ih (List.nodup_cons.mp distinct).2 (stage+1)
        (restoreNext (Snapshot.ofTree comparator) tree record start states) head.1 headOrdered tailAbsent
        (WinnerCredit.run state actions) headSynced
      simpa only [program, WinnerCredit.run_append, freshRestorePorts] using tail

noncomputable def administration {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → States n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : States n) : List (Action n) :=
  WinnerCredit.batch (RestorationJournal.labels comparator K states) ++ program comparator tree K reader ports stage start states

theorem administration_erases {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → States n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : States n) :
    erase (administration comparator tree K reader ports stage start states) =
      RestorationJournal.administration comparator tree K reader ports stage start states := by
  rw [administration, erase_append, batch_erases, program_erases]
  rfl

theorem administration_administrative {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → States n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : States n) :
    Administrative (administration comparator tree K reader ports stage start states) :=
  (administrative_append ..).mpr ⟨batch_administrative _, program_administrative comparator tree K reader ports stage start states⟩

theorem administration_pointer {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → States n → External n → External n → Entry)
    (keys : ∀ stage current record owner, (reader stage current record owner).key = record.val)
    (ports : List (External n)) (distinct : ports.Nodup) (stage start : ℕ)
    (states : States n) (ordered : Ordered states)
    (absent : ∀ record ∈ ports, ¬ GreedyMerge.BlockCoverage.Represented states record.val)
    (state : State n) (synced : MembershipPointer.Synced state.ticket states) :
    MembershipPointer.Synced (WinnerCredit.run state (administration comparator tree K reader ports stage start states)).ticket
      (freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states).states := by
  rw [administration, WinnerCredit.run_append]
  exact program_pointer comparator tree K reader keys ports distinct stage start states ordered absent _
    (by rw [batch_ticket]; exact synced)

end Greedy.TicketJournal
