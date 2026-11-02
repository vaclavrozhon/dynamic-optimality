import ChaCha.Paper20261030.PathDecomposition

/-! The preferred endpoint occupies a specific actual port of the balanced
root auxiliary. The position counts right-going preferred reference edges,
and the port is exactly the original terminal leaf, including its record. -/

namespace ChaCha.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations

variable {α κ : Type*} {β : κ → Type*}

def terminalIndex (right : Record (β := β) → Bool) : Source α (Record (β := β)) → Nat
  | .leaf .. => 0
  | .fork record l r => if right record then 1 + terminalIndex right r else terminalIndex right l

def terminalSource (right : Record (β := β) → Bool) : Source α (Record (β := β)) → Source α (Record (β := β))
  | .leaf key record => .leaf key record
  | .fork record l r => if right record then terminalSource right r else terminalSource right l

theorem terminalIndex_bound (right : Record (β := β) → Bool) (source : Source α (Record (β := β))) :
    terminalIndex right source ≤ (PathPorts.skeleton right source).size := by
  induction source with
  | leaf => exact Nat.le_refl _
  | fork record l r ihl ihr =>
    cases hd : right record <;>
      simp only [terminalIndex,PathPorts.skeleton,hd,Bool.false_eq_true,if_false,if_true,MTR.Tree.size] <;> omega

theorem Represents.terminalIndex_bound [Ord κ] {right : Record (β := β) → Bool}
    {source : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right source c) : terminalIndex right source ≤ c.core.size := by
  rw [h.size]
  exact PathDecomposition.terminalIndex_bound right source

theorem Represents.terminal_port [Ord κ] {right : Record (β := β) → Bool}
    {source : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right source c) : c.ports (terminalIndex right source) = terminalSource right source := by
  induction h with
  | leaf marked same => exact same.ports 0 (Nat.zero_le _)
  | @left record l r lc rc c direction clean hl hr same ihl ihr =>
    have hi := hl.terminalIndex_bound
    have hb : terminalIndex right l ≤ c.core.size := by rw [same.size,append_size]; omega
    simp only [terminalIndex,terminalSource,direction,Bool.false_eq_true,if_false]
    rw [same.ports _ hb]
    simpa only [append,if_pos hi] using ihl
  | @right record l r lc rc c direction clean hl hr same ihl ihr =>
    have hi := hr.terminalIndex_bound
    have hb : 1 + terminalIndex right r ≤ c.core.size := by rw [same.size,prepend_size]; omega
    simp only [terminalIndex,terminalSource,direction,if_true]
    rw [same.ports _ hb]
    simpa only [prepend,show ¬ 1 + terminalIndex right r = 0 by omega,if_false,
      Nat.add_sub_cancel_left] using ihr

end ChaCha.Paper20261030.PathDecomposition
