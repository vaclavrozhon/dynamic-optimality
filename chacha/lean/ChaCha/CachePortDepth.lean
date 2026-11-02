import ChaCha.MTR
import Lean.Elab.Tactic.Omega

/-!
# Actual rotation depths and the cost of overwriting a cached finger

Every state contains an ordered BST and a successful actual search-depth
certificate. A rotation step is an actual local BST rotation in an arbitrary
subtree. An overwrite physically pays old depth plus new depth. The finite
trace bound is therefore not conditional on an assumed depth-variation law.

The constant-finger simulation and the comparison of a newly accessed key's
final depth with its genuine transaction work remain external arguments.
-/

namespace ChaCha.CachePortDepth

open MTR MTR.Tree

/-- Failed searches agree; successful depths differ by at most one. -/
def CloseDepth : Option Nat → Option Nat → Prop
  | none, none => True
  | some d, some e => e ≤ d + 1 ∧ d ≤ e + 1
  | _, _ => False

theorem CloseDepth.refl (d : Option Nat) : CloseDepth d d := by
  cases d <;> simp [CloseDepth]

theorem CloseDepth.symm {d e : Option Nat} (h : CloseDepth d e) : CloseDepth e d := by
  cases d <;> cases e <;> simp_all [CloseDepth, and_comm]

theorem CloseDepth.succ {d e : Option Nat} (h : CloseDepth d e) :
    CloseDepth (d.map Nat.succ) (e.map Nat.succ) := by
  cases d <;> cases e <;> simp_all [CloseDepth]

theorem closeDepth_rotateRight (A B C : Tree Int) (x y q : Int) (hxy : x < y) :
    CloseDepth (searchDepth q (.node (.node A x B) y C))
      (searchDepth q (.node A x (.node B y C))) := by
  rcases lt_trichotomy q x with hqx | hqx | hxq
  · have hqy : q < y := lt_trans hqx hxy
    simp only [searchDepth, hqy, hqx, ↓reduceIte]
    cases h : searchDepth q A <;> simp [CloseDepth]
  · subst q
    simp [searchDepth, hxy, CloseDepth]
  · have hnqx : ¬ q < x := by omega
    rcases lt_trichotomy q y with hqy | hqy | hyq
    · simp [searchDepth, hqy, hxq, hnqx, CloseDepth.refl]
    · subst q
      simp [searchDepth, hxy, hnqx, CloseDepth]
    · have hnqy : ¬ q < y := by omega
      simp only [searchDepth, hnqy, hyq, hnqx, hxq, ↓reduceIte]
      cases h : searchDepth q C <;> simp [CloseDepth]

/-- One actual local rotation, at any depth. The local key inequality is
explicit; our execution states below additionally certify global BST order. -/
inductive Rotation : Tree Int → Tree Int → Prop
  | right (A B C : Tree Int) (x y : Int) (hxy : x < y) :
      Rotation (.node (.node A x B) y C) (.node A x (.node B y C))
  | left (A B C : Tree Int) (x y : Int) (hxy : x < y) :
      Rotation (.node A x (.node B y C)) (.node (.node A x B) y C)
  | underLeft {A A' : Tree Int} (x : Int) (B : Tree Int) (h : Rotation A A') :
      Rotation (.node A x B) (.node A' x B)
  | underRight (A : Tree Int) (x : Int) {B B' : Tree Int} (h : Rotation B B') :
      Rotation (.node A x B) (.node A x B')

theorem Rotation.closeDepth {T U : Tree Int} (h : Rotation T U) (q : Int) :
    CloseDepth (searchDepth q T) (searchDepth q U) := by
  induction h with
  | right A B C x y hxy => exact closeDepth_rotateRight A B C x y q hxy
  | left A B C x y hxy => exact (closeDepth_rotateRight A B C x y q hxy).symm
  | underLeft x B h ih =>
    by_cases hqx : q < x
    · simpa only [searchDepth, hqx, ↓reduceIte] using ih.succ
    · simp only [searchDepth, hqx, ↓reduceIte]
      split <;> exact CloseDepth.refl _
  | underRight A x h ih =>
    by_cases hqx : q < x
    · simp only [searchDepth, hqx, ↓reduceIte]
      exact CloseDepth.refl _
    · by_cases hxq : x < q
      · simpa only [searchDepth, hqx, hxq, ↓reduceIte] using ih.succ
      · simp [searchDepth, hqx, hxq, CloseDepth]

theorem Rotation.successful_depth {T U : Tree Int} (h : Rotation T U)
    (q : Int) (d : Nat) (hd : searchDepth q T = some d) :
    ∃ e, searchDepth q U = some e ∧ e ≤ d + 1 ∧ d ≤ e + 1 := by
  have hc := h.closeDepth q
  rw [hd] at hc
  cases he : searchDepth q U with
  | none => simp [he, CloseDepth] at hc
  | some e => exact ⟨e, rfl, by simpa [he, CloseDepth] using hc⟩

structure State where
  tree : Tree Int
  key : Int
  depth : Nat
  ordered : Ordered tree
  found : searchDepth key tree = some depth

/-- The two charged event types. Reads leave the state unchanged and add their
unit request costs outside this movement bound. -/
inductive Step : State → State → Nat → Nat → Nat → Prop
  | rotate (s t : State) (hrot : Rotation s.tree t.tree) (hkey : t.key = s.key) :
      Step s t 0 1 0
  | overwrite (s t : State) (htree : t.tree = s.tree) :
      Step s t (s.depth + t.depth) 0 t.depth

theorem Step.potential {s t : State} {moves rotations newDepth : Nat}
    (h : Step s t moves rotations newDepth) :
    moves + t.depth ≤ s.depth + rotations + 2 * newDepth := by
  cases h with
  | rotate hrot hkey =>
    have hc := hrot.closeDepth s.key
    rw [s.found, ← hkey, t.found] at hc
    simp only [CloseDepth] at hc
    omega
  | overwrite htree => omega

/-- Finite chronological traces count actual cache movement, actual comparator
rotations, and the sum of depths of the newly assigned actual keys. -/
inductive Trace : State → State → Nat → Nat → Nat → Prop
  | nil (s : State) : Trace s s 0 0 0
  | cons {s t u : State} {m r d M R D : Nat}
      (step : Step s t m r d) (tail : Trace t u M R D) :
      Trace s u (m + M) (r + R) (d + D)

theorem Trace.potential {s t : State} {moves rotations newDepth : Nat}
    (h : Trace s t moves rotations newDepth) :
    moves + t.depth ≤ s.depth + rotations + 2 * newDepth := by
  induction h with
  | nil s => omega
  | cons step tail ih =>
    have hs := step.potential
    omega

theorem Trace.movement_le {s t : State} {moves rotations newDepth : Nat}
    (h : Trace s t moves rotations newDepth) :
    moves ≤ s.depth + rotations + 2 * newDepth := by
  have hp := h.potential
  omega

end ChaCha.CachePortDepth
