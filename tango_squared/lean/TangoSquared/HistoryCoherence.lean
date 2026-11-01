import TangoSquared.AmbientSimulation
import TangoSquared.NormalizedWords
import TangoSquared.ExecutionFacts

/-!
# Physical representatives and last-access preferences

The initialized analytical preference is read from the actual initial BST.
Along a successful MTR execution it agrees with the last-access definition.
-/

namespace TangoSquared.Primary
open MTR MTR.Tree NormalizedWords

def initialPreference (H : Nat) (t : Tree Key) (u : Key) : Bool :=
  (bstPreference H t u).getD false

theorem bstPreference_step {H : Nat} {t : Tree Key} {x u : Key}
    (hx : x.length = H) (hs : ∃ d, searchDepth x t = some d) :
    bstPreference H (moveToRoot x t) u =
      if u.IsPrefix x then branch u x else bstPreference H t u := by
  obtain ⟨d, hd⟩ := hs
  have hr := representative_moveToRoot (cellMin H u) (cellMax H u) x t d hd
  unfold bstPreference
  rw [hr]
  have hp : InInterval (cellMin H u) (cellMax H u) x ↔ u.IsPrefix x :=
    (prefix_iff_mem_cell hx).symm
  simp only [hp]
  split_ifs <;> rfl

theorem bstPreference_step_of_branch {H : Nat} {t : Tree Key} {x u : Key} {b : Bool}
    (hx : x.length = H) (hs : ∃ d, searchDepth x t = some d)
    (hb : branch u x = some b) : bstPreference H (moveToRoot x t) u = some b := by
  rw [bstPreference_step hx hs, if_pos (prefix_of_branch_some hb), hb]

theorem bstPreference_history {H : Nat} {t : Tree Key} {xs : List Key} {u : Key}
    (hu : u ∈ owners H) (hs : Successful t xs)
    (hleaves : ∀ x ∈ xs, x.length = H) :
    (bstPreference H (run t xs) u).getD false =
      preference (initialPreference H t) xs u := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    have hs' := (successful_append t xs [x]).mp hs
    have hx : x.length = H := hleaves x (by simp)
    have ih' := ih hs'.1 (fun y hy => hleaves y (by simp [hy]))
    rw [run_append]
    change (bstPreference H (moveToRoot x (run t xs)) u).getD false = _
    rw [bstPreference_step hx hs'.2.1]
    by_cases hp : u.IsPrefix x
    · have hlen : u.length < x.length := by rw [hx]; exact (mem_owners u H).mp hu
      obtain ⟨b, hb⟩ := branch_some_of_prefix hp hlen
      simp only [if_pos hp, hb, Option.getD_some]
      exact (preference_append_last _ xs x u b hb).symm
    · simp only [if_neg hp]
      rw [ih']
      have hb : branch u x = none := by simp [branch, hp]
      simp [preference, hb]

/-- Normalization proved from actual BST representative changes implies the
concrete last-access normalization used by return and witness arguments. -/
theorem ambientNormalized_history {H : Nat} {t : Tree Key} {xs : List Key}
    (ha : AmbientNormalized H t xs) (hs : Successful t xs)
    (hleaves : ∀ x ∈ xs, x.length = H) :
    Normalized (initialPreference H t) H xs := by
  intro history x future heq
  have ha' : AmbientNormalized H (run t history) (x :: future) := by
    exact ((ambientNormalized_append H t history (x :: future)).mp (heq ▸ ha)).2
  have hs' := (successful_append t history (x :: future)).mp (heq ▸ hs)
  have hx : x.length = H := hleaves x (by rw [heq]; simp)
  have histLeaves : ∀ y ∈ history, y.length = H := by
    intro y hy
    apply hleaves y
    rw [heq]
    simp [hy]
  have hchanged (u : Key) (hu : u ∈ owners H)
      (hf : Flips (initialPreference H t) history x u) :
      bstPreference H (moveToRoot x (run t history)) u ≠ bstPreference H (run t history) u := by
    obtain ⟨b, hb, hneq⟩ := hf
    have hnew := bstPreference_step_of_branch hx hs'.2.1 hb
    intro he
    apply hneq
    have hc := bstPreference_history hu hs'.1 histLeaves
    rw [← he, hnew] at hc
    exact hc.symm
  intro u hu v hv hfu hfv
  exact ha'.1 u hu v hv (hchanged u hu hfu) (hchanged v hv hfv)

end TangoSquared.Primary
