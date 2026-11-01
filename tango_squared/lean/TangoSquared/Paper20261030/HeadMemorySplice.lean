import TangoSquared.Paper20261030.DormantPreferences

/-!
# Persistent memory transfer at an actual primary head switch

The two preferred endpoints have the same primary ancestors through the
switch depth. Consequently the new active secondary state keeps the old
prefix memories and takes the incoming suffix memories. The old state is
already prepared at the new sentinel, and no genuine suffix memory is
changed or reinitialized by the switch.
-/

namespace TangoSquared.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

theorem HeadStep.endpoint_prefix {x : α} {d : Nat} {t u : PrefRouter α}
    (h : HeadStep x d t u) (hn : t.leaves.Nodup) :
    (t.searchPath t.terminal).take d = (u.searchPath u.terminal).take d := by
  induction h with
  | leftRoot => rfl
  | rightRoot => rfl
  | @leftDown d l l' r h ih =>
    obtain ⟨hnl,_,_⟩ := List.nodup_append.mp hn
    simpa only [PrefRouter.terminal,Bool.false_eq_true,↓reduceIte,PrefRouter.searchPath,
      if_pos l.terminal_mem,if_pos l'.terminal_mem,List.take_succ_cons] using
        congrArg (false :: ·) (ih hnl)
  | @rightDown d r r' l hl h ih =>
    obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.mp hn
    have htr : r.terminal ∉ l.leaves := fun hm => hdis _ hm _ r.terminal_mem rfl
    have hnew : r'.terminal ∈ r.leaves := by rw [← h.leaves]; exact r'.terminal_mem
    have htr' : r'.terminal ∉ l.leaves := fun hm => hdis _ hm _ hnew rfl
    simpa only [PrefRouter.terminal,↓reduceIte,PrefRouter.searchPath,if_neg htr,if_neg htr',
      if_pos r.terminal_mem,if_pos r'.terminal_mem,List.take_succ_cons] using
        congrArg (true :: ·) (ih hnr)

theorem HeadStep.endpoint_owner {x : α} {d a : Nat} {t u : PrefRouter α}
    (h : HeadStep x d t u) (hn : t.leaves.Nodup) (ha : a ≤ d) :
    (t.searchPath t.terminal).take a = (u.searchPath u.terminal).take a := by
  have hp := congrArg (List.take a) (h.endpoint_prefix hn)
  simpa only [List.take_take,Nat.min_eq_left ha] using hp

end TangoSquared.PreferredProjection.PrefRouter

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection

variable {α : Type*} [DecidableEq α]

def spliceBits (cutoff : Nat) (prefixState suffixState : DepthSplit → Bool) : DepthSplit → Bool :=
  fun s => if s.lo ≤ cutoff then prefixState s else suffixState s

theorem head_owner_splice {x : α} {d : Nat} {t u : PrefRouter α}
    (h : PrefRouter.HeadStep x d t u) (hn : t.leaves.Nodup) (preference : MemoryKey → Bool) :
    ownerBits u u.terminal preference =
      spliceBits d (ownerBits t t.terminal preference) (ownerBits t u.terminal preference) := by
  funext s
  by_cases hs : s.lo ≤ d
  · simp only [spliceBits,if_pos hs,ownerBits,h.endpoint_owner hn hs]
  · simp only [spliceBits,if_neg hs,ownerBits,h.searchPath u.terminal]

theorem depthWrite_suffix_unchanged (t : PrefRouter α) (x endpoint : α) (d : Nat)
    (preference : MemoryKey → Bool) (s : DepthSplit) (hs : d < s.lo) :
    ownerBits t endpoint (advanceDepth t x d preference) s = ownerBits t endpoint preference s := by
  simp [ownerBits,advanceDepth,depthWrite,show ¬s.lo ≤ d by omega]

/-- Exact prefix/suffix transfer for the concrete persistent array. The
old prefix has just received the secondary access at the switch depth;
the incoming genuine suffix keeps its pre-switch bits. -/
theorem head_memory_transfer {x : α} {d : Nat} {t u : PrefRouter α}
    (h : PrefRouter.HeadStep x d t u) (hn : t.leaves.Nodup) (preference : MemoryKey → Bool) :
    ownerBits u u.terminal (advanceDepth t x d preference) =
      spliceBits d (intervalUpdate d (ownerBits t t.terminal preference))
        (ownerBits t u.terminal preference) := by
  rw [head_owner_splice h hn,ownerBits_advance h hn]
  funext s
  by_cases hs : s.lo ≤ d
  · simp only [spliceBits,if_pos hs]
  · simp only [spliceBits,if_neg hs]
    exact depthWrite_suffix_unchanged t x u.terminal d preference s (by omega)

theorem old_tail_prepared {x : α} {d : Nat} {t u : PrefRouter α}
    (h : PrefRouter.HeadStep x d t u) (hn : t.leaves.Nodup) (preference : MemoryKey → Bool) :
    ownerBits u t.terminal (advanceDepth t x d preference) =
      intervalUpdate d (ownerBits t t.terminal preference) := by
  have he : ownerBits u t.terminal (advanceDepth t x d preference) =
      ownerBits t t.terminal (advanceDepth t x d preference) := by
    funext s
    simp only [ownerBits,h.searchPath t.terminal]
  rw [he,ownerBits_advance h hn]

theorem prepared_boundary_agreement (old incoming : DepthSplit → Bool) (d : Nat)
    (s : DepthSplit) (hs : s.lo ≤ d ∧ d ≤ s.hi) :
    intervalUpdate d old s = intervalUpdate d incoming s := by
  simp [intervalUpdate,hs]

end TangoSquared.Paper20261030.Secondary
