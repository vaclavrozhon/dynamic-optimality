import ChaCha.Paper20261030.ChargedRearrangements
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-!
# Building a balanced auxiliary tree from its existing records

`assemble` preserves the supplied record word exactly. Its input physical
representation is a right spine containing those records, with correct
cached sizes. The charged trace rebalances this spine; it neither creates
nor discards a key or payload. Preparing the spine from the original-key
BST and distributing records among components are separate initialization
obligations.
-/

namespace ChaCha.Paper20261030.Auxiliary.Metadata

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {α : Type*} {β : α → Type*}

def assemble : (entries : List (Sigma β)) → Impl.Tree α β entries.length
  | [] => ⟨.leaf,.leaf,rfl⟩
  | entry :: entries =>
    let tail := assemble entries
    let result := insertMin entry.1 entry.2 tail.impl tail.balanced_impl
    ⟨result.impl,result.balanced_impl,by rw [result.size_impl,tail.size_impl]; simp [Nat.add_comm]⟩

theorem assemble_word [Ord α] (entries : List (Sigma β)) :
    (assemble entries).impl.toListModel = entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [assemble,toListModel_insertMin,ih]

def spine : List (Sigma β) → Impl α β
  | [] => .leaf
  | entry :: entries => bin entry.1 entry.2 .leaf (spine entries)

theorem spine_size (entries : List (Sigma β)) : (spine entries).size = entries.length := by
  induction entries <;> simp_all [spine,bin,Impl.size_leaf,Impl.size_inner,Nat.add_comm]

theorem assemble_charged (entries : List (Sigma β)) :
    ObservedRearranges (spine entries) (assemble entries).impl
      ((495 * Nat.clog 2 (entries.length + 1) + 78) * entries.length) := by
  induction entries with
  | nil => exact fun _ => ⟨[],0,.nil _,le_rfl⟩
  | cons entry entries ih =>
    have excursion : ObservedRearranges
        (bin entry.1 entry.2 .leaf (spine entries))
        (bin entry.1 entry.2 .leaf (assemble entries).impl)
        ((495 * Nat.clog 2 (entries.length + 1) + 78) * entries.length + 2) := by
      cases entries with
      | nil => exact fun _ => ⟨[],0,.nil _,Nat.zero_le _⟩
      | cons next rest =>
        exact ih.bin_right (by simp [spine,bin]) (by rw [spine_size,(assemble _).size_impl])
    have joined := insertMin_charged_log (0 + 1 + (assemble entries).impl.size)
      entry.1 entry.2 (assemble entries).impl (assemble entries).balanced_impl
    have all := excursion.trans joined
    change ObservedRearranges (bin entry.1 entry.2 .leaf (spine entries))
      (insertMin entry.1 entry.2 (assemble entries).impl (assemble entries).balanced_impl).impl _
    apply all.mono
    have hm := Nat.clog_monotone 2 (show entries.length + 1 ≤ (entry :: entries).length + 1 by simp)
    have hp := Nat.mul_le_mul_right entries.length
      (show 495 * Nat.clog 2 (entries.length + 1) + 78 ≤
        495 * Nat.clog 2 ((entry :: entries).length + 1) + 78 by omega)
    rw [(assemble entries).size_impl]
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at hp hm ⊢
    omega

end ChaCha.Paper20261030.Auxiliary.Metadata
