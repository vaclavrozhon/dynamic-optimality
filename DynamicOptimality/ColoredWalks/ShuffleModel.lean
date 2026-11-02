import DynamicOptimality.ColoredWalks.ShuffleEncodingInterface
import Mathlib.Data.Finset.Basic

/-! # Shuffles of nearest-neighbor walks on fixed ordered subsets

The color identifies a source walk. Its allowed key set remains fixed
throughout the interleaving. A step may stay at the same key or move to
one of its two neighbors in that subset. The first event of each source
chooses its starting key freely; later events retain that source's previous
position even while other sources are served.
-/

namespace DynamicOptimality.ColoredWalks

variable {α : Type*} [LinearOrder α]

structure NeighborStep (keys : Finset α) (first last : α) : Prop where
  first_mem : first ∈ keys
  last_mem : last ∈ keys
  consecutive : ∀ key ∈ keys, key ≤ min first last ∨ max first last ≤ key

theorem NeighborStep.symm {keys : Finset α} {first last : α}
    (step : NeighborStep keys first last) : NeighborStep keys last first :=
  ⟨step.last_mem,step.first_mem,by simpa only [min_comm,max_comm] using step.consecutive⟩

theorem NeighborStep.stay {keys : Finset α} {key : α} (member : key ∈ keys) :
    NeighborStep keys key key := by
  refine ⟨member,member,?_⟩
  intro other present
  simpa only [min_self,max_self] using le_total other key

inductive WalkFrom {k : Nat} (sets : Fin k → Finset α) :
    (Fin k → Option α) → List (Fin k × α) → Prop
  | nil (positions : Fin k → Option α) : WalkFrom sets positions []
  | cons {positions : Fin k → Option α} {events : List (Fin k × α)}
      (color : Fin k) (key : α) (present : key ∈ sets color)
      (step : ∀ previous, positions color = some previous → NeighborStep (sets color) previous key)
      (rest : WalkFrom sets (Function.update positions color (some key)) events) :
      WalkFrom sets positions ((color,key)::events)

/-- The event labels specify the interleaving; no occurrences are dropped. -/
def ShuffleWalk {k : Nat} (sets : Fin k → Finset α) (events : List (Fin k × α)) : Prop :=
  WalkFrom sets (fun _ => none) events

theorem WalkFrom.members {k : Nat} {sets : Fin k → Finset α}
    {positions : Fin k → Option α} {events : List (Fin k × α)}
    (walk : WalkFrom sets positions events) : ∀ event ∈ events, event.2 ∈ sets event.1 := by
  induction walk with
  | nil => simp
  | cons color key present step rest ih =>
      intro event member
      rcases List.mem_cons.mp member with rfl | later
      · exact present
      · exact ih event later

end DynamicOptimality.ColoredWalks
