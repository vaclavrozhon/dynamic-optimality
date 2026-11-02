import ChaCha.Paper20261030.PackedNavigationDecision
import ChaCha.Paper20261030.ForestNavigationProgram

/-! Executing a descent simultaneously in every color projection. The
fixed program moves exactly the colors in the intersection of the two
child masks. Active and parked cursors for every other color stay put.
Acquisition of these masks through a local read is composed separately.
-/

namespace ChaCha.Paper20261030.PackedDescentController

open ColoredStorage SourcePointer ForestLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C] [Fintype C]

def action (right : Bool) : Move := if right then .right else .left

def child (right : Bool) (l r : Source α ρ) (record : ρ) (outside : List (Frame α ρ)) : Cursor α ρ :=
  if right then ⟨r,.right l record::outside⟩ else ⟨l,.left record r::outside⟩

theorem descend (color : α → C) (right : Bool) (l r : Source α ρ) (record : ρ) (outside)
    (forest : ProjectionForest.State C α ρ)
    (represented : ProjectionForest.Represents color ⟨.fork record l r,outside⟩ forest) :
    ∃ target,
      Run (ForestNavigationController.program (action right)) ((l.support color ∩ r.support color).sort (· ≤ ·))
        forest [] target [] (l.support color ∩ r.support color).card ∧
      ProjectionForest.Represents color (child right l r record outside) target ∧
      (l.support color ∩ r.support color).card ≤ Fintype.card C := by
  classical
  let selected := l.support color ∩ r.support color
  have sameTree : (child right l r record outside).tree = (Cursor.tree ⟨.fork record l r,outside⟩) := by
    cases right <;> rfl
  have each : ∀ q, ∃ actual,
      ProjectionForest.RepresentsAt color q (child right l r record outside) actual ∧
      (q ∈ selected → ∃ old fresh, forest q = some old ∧ actual = some fresh ∧
        SourceLocalProgram.navigate (action right) old = some fresh) ∧
      (q ∉ selected → actual = forest q) := by
    intro q
    have atRep := represented q
    cases location : forest q with
    | none =>
      rw [location] at atRep
      have inactive : q ∉ selected := by
        intro member
        have inFocus : q ∈ (Source.fork record l r).support color :=
          Finset.mem_union_left _ (Finset.mem_inter.mp member).1
        exact atRep (ProjectionForest.support_focus color (.fork record l r) outside inFocus)
      exact ⟨none,by simpa only [ProjectionForest.RepresentsAt,sameTree] using atRep,
        fun impossible => False.elim (inactive impossible),fun _ => rfl⟩
    | some physical =>
      rw [location] at atRep
      by_cases active : q ∈ selected
      · have moved : ∃ fresh, SourceLocalProgram.navigate (action right) physical = some fresh ∧
            ColoredStorage.Represents color q (child right l r record outside) fresh := by
          cases right with
          | false => exact left_active color q l r record outside (Finset.mem_inter.mp active) atRep
          | true => exact right_active color q l r record outside (Finset.mem_inter.mp active) atRep
        obtain ⟨fresh,move,freshRep⟩ := moved
        exact ⟨some fresh,freshRep,fun _ => ⟨physical,fresh,rfl,rfl,move⟩,
          fun absent => False.elim (absent active)⟩
      · have idle : q ∉ l.support color ∨ q ∉ r.support color := by
          by_cases left : q ∈ l.support color
          · exact Or.inr (fun right => active (Finset.mem_inter.mpr ⟨left,right⟩))
          · exact Or.inl left
        have freshRep : ColoredStorage.Represents color q (child right l r record outside) physical := by
          cases right with
          | false => exact left_idle color q l r record outside idle atRep
          | true => exact right_idle color q l r record outside idle atRep
        exact ⟨some physical,freshRep,fun impossible => False.elim (active impossible),fun _ => rfl⟩
  choose target targetRep selectedMove unchanged using each
  have run := ForestNavigationController.move (action right) (selected.sort (· ≤ ·)) forest target (selected.sort_nodup (· ≤ ·))
    (fun q member => selectedMove q ((Finset.mem_sort (· ≤ ·)).mp member))
    (fun q absent => (unchanged q (fun member => absent ((Finset.mem_sort (· ≤ ·)).mpr member))).symm)
  exact ⟨target,by simpa only [Finset.length_sort] using run,targetRep,Finset.card_le_univ _⟩

end ChaCha.Paper20261030.PackedDescentController
