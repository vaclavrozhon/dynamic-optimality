import ChaCha.Paper20261030.SequentialMemory
import ChaCha.Paper20261030.SecondaryReference

/-!
# Decoding persistent bits as an actual secondary preferred tree

Each internal depth-reference interval has one preference bit. Updating
the intervals containing a requested depth is exactly ordinary Tango
access on the decoded tree. For the active primary path, the persistent
owner-indexed writes implement precisely this update before a head switch.
-/

namespace ChaCha.Paper20261030.Secondary

open PreferredProjection

def decodeDepth : {a b : Nat} → DepthTree a b → (DepthSplit → Bool) → PrefRouter Nat
  | _,_,.leaf a,_ => .leaf a
  | a,b,.node c _ _ l r,preference =>
      .fork (preference ⟨a,c,b⟩) (decodeDepth l preference) (decodeDepth r preference)

theorem decodeDepth_mem {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool)
    (d : Nat) : d ∈ (decodeDepth reference preference).leaves ↔ a ≤ d ∧ d ≤ b := by
  induction reference with
  | leaf a => simp only [decodeDepth,PrefRouter.leaves,List.mem_singleton]; omega
  | @node a b c ha hb l r ihl ihr =>
    simp only [decodeDepth,PrefRouter.leaves,List.mem_append,ihl,ihr]
    omega

def intervalUpdate (d : Nat) (preference : DepthSplit → Bool) : DepthSplit → Bool :=
  fun s => if s.lo ≤ d ∧ d ≤ s.hi then decide (s.cut < d) else preference s

theorem decodeDepth_access {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (d : Nat) :
    decodeDepth reference (intervalUpdate d preference) = (decodeDepth reference preference).access d := by
  induction reference with
  | leaf a => rfl
  | @node a b c ha hb l r ihl ihr =>
    have hml := decodeDepth_mem l preference d
    have hmr := decodeDepth_mem r preference d
    by_cases hl : a ≤ d ∧ d ≤ c
    · have hnr : d ∉ (decodeDepth r preference).leaves := by rw [hmr]; omega
      have hracc := PrefRouter.access_absent d (decodeDepth r preference) hnr
      simp only [decodeDepth,ihl,ihr,PrefRouter.access,if_pos (hml.mpr hl),hracc,intervalUpdate]
      simp [show a ≤ d ∧ d ≤ b by omega,show ¬c < d by omega]
    · by_cases hr : c + 1 ≤ d ∧ d ≤ b
      · have hnl : d ∉ (decodeDepth l preference).leaves := by rw [hml]; exact hl
        have hlacc := PrefRouter.access_absent d (decodeDepth l preference) hnl
        simp only [decodeDepth,ihl,ihr,PrefRouter.access,if_neg hnl,if_pos (hmr.mpr hr),hlacc,intervalUpdate]
        simp [show a ≤ d ∧ d ≤ b by omega,show c < d by omega]
      · have hnl : d ∉ (decodeDepth l preference).leaves := by rw [hml]; exact hl
        have hnr : d ∉ (decodeDepth r preference).leaves := by rw [hmr]; exact hr
        have hlacc := PrefRouter.access_absent d (decodeDepth l preference) hnl
        have hracc := PrefRouter.access_absent d (decodeDepth r preference) hnr
        simp only [decodeDepth,ihl,ihr,PrefRouter.access,if_neg hnl,if_neg hnr,hlacc,hracc,intervalUpdate]
        simp [show ¬(a ≤ d ∧ d ≤ b) by omega]

def ownerBits {α : Type*} [DecidableEq α] (primary : PrefRouter α) (endpoint : α)
    (preference : MemoryKey → Bool) : DepthSplit → Bool :=
  fun s => preference (s,(primary.searchPath endpoint).take s.lo)

theorem ownerBits_advance {α : Type*} [DecidableEq α] {x : α} {d : Nat} {t u : PrefRouter α}
    (h : PrefRouter.HeadStep x d t u) (hn : t.leaves.Nodup) (preference : MemoryKey → Bool) :
    ownerBits t t.terminal (advanceDepth t x d preference) =
      intervalUpdate d (ownerBits t t.terminal preference) := by
  funext s
  by_cases hd : s.lo ≤ d ∧ d ≤ s.hi
  · have hp : ((t.searchPath t.terminal).take s.lo).IsPrefix (t.searchPath x) := by
      rw [h.memory_owner hn hd.1]
      exact List.take_prefix _ _
    simp [ownerBits,advanceDepth,depthWrite,intervalUpdate,hp,hd]
  · simp [ownerBits,advanceDepth,depthWrite,intervalUpdate,hd]

/-- The write phase immediately before an actual primary head switch is
an ordinary secondary access on the active owner's decoded reference. -/
theorem head_write_is_secondary_access {α : Type*} [DecidableEq α] {x : α} {d a b : Nat}
    {t u : PrefRouter α} (h : PrefRouter.HeadStep x d t u) (hn : t.leaves.Nodup)
    (reference : DepthTree a b) (preference : MemoryKey → Bool) :
    decodeDepth reference (ownerBits t t.terminal (advanceDepth t x d preference)) =
      (decodeDepth reference (ownerBits t t.terminal preference)).access d := by
  rw [ownerBits_advance h hn,decodeDepth_access]

end ChaCha.Paper20261030.Secondary
