import TangoSquared.Paper20261030.SecondaryWords
import TangoSquared.Paper20261030.PrimaryRecency

/-!
# First secondary writes are actual LCA directions

Only exit depths inside a fragment's interval write its preference. For an
owner at the local root, `b` is its final depth and `c` its split depth.
Sorted exits imply that the first write is determined by the first exit,
or that there is no write when the first exit lies below the interval.
-/

namespace TangoSquared.Paper20261030.Secondary

open FlipAccounting PreferredProjection

theorem visitBlock_head (c : Nat) (ds : List Nat) (hs : ds.Pairwise (· < ·)) :
    (visitBlock c ds).map Block.head = ds.head?.map (fun d => decide (c < d)) := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    by_cases hd : d ≤ c
    · have hlow : lowDepths c (d :: ds) ≠ [] := by simp [lowDepths,hd]
      have hcd : ¬ c < d := by omega
      unfold visitBlock
      rw [if_neg hlow]
      split_ifs <;> simp [Block.head,hcd]
    · have hcd : c < d := by omega
      have hlow : lowDepths c (d :: ds) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e he
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp he with rfl | he
        · exact hd
        · have := hhead e he; omega
      have hhigh : highDepths c (d :: ds) ≠ [] := by simp [highDepths,hcd]
      simp [visitBlock,hlow,hhigh,Block.head,hcd]

theorem lowDepths_head (b : Nat) (ds : List Nat) (hs : ds.Pairwise (· < ·)) :
    (lowDepths b ds).head? = ds.head?.filter (fun d => decide (d ≤ b)) := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    by_cases hd : d ≤ b
    · simp [lowDepths,hd,Option.filter]
    · have hn : lowDepths b (d :: ds) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e he
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp he with rfl | he
        · exact hd
        · have := (List.pairwise_cons.mp hs).1 e he; omega
      simp [hn,hd,Option.filter]

theorem lowDepths_increasing (b : Nat) (ds : List Nat) (hs : ds.Pairwise (· < ·)) :
    (lowDepths b ds).Pairwise (· < ·) := hs.filter _

theorem truncated_visit_head (c b H : Nat) (hb : b < H) (ds : List Nat)
    (hs : ds.Pairwise (· < ·)) :
    (visitBlock c (lowDepths b ds)).map Block.head =
      if ds.headD H ≤ b then some (decide (c < ds.headD H)) else none := by
  rw [visitBlock_head c _ (lowDepths_increasing b ds hs),lowDepths_head b ds hs]
  cases ds with
  | nil => simp [show ¬ H ≤ b by omega]
  | cons d ds => by_cases hd : d ≤ b <;> simp [hd,Option.filter] <;> omega

/-- The head of the actual secondary write block after a previous local
request agrees with the fragment's LCA update rule. -/
theorem next_visit_head {α : Type*} [DecidableEq α] {t : PrefRouter α}
    {H c b : Nat} (hp : t.Perfect H) (hn : t.leaves.Nodup) (hb : b < H)
    {p x : α} (hprev : p ∈ t.leaves) (hx : x ∈ t.leaves) :
    (visitBlock c (lowDepths b ((t.access p).exitDepths x))).map Block.head =
      if t.referenceLCA p x ≤ b then some (decide (c < t.referenceLCA p x)) else none := by
  rw [truncated_visit_head c b H hb _ ((t.access p).exitDepths_increasing x),
    PrefRouter.next_first_exit_lca hp hn hprev hx]

end TangoSquared.Paper20261030.Secondary
