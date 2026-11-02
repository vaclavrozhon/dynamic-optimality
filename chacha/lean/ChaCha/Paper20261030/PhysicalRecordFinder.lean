import ChaCha.Paper20261030.PhysicalRecordFinderSound
import Mathlib.Data.Finset.Sort

/-! Complete local search of the bounded physical neighborhood. It
terminates at the wanted record within five operations per color, using
actual current-node reads and the checked parent observation program.
The specialized endpoint establishes the manuscript's parent lookup.
-/

namespace ChaCha.Paper20261030.PhysicalRecordFinder

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C]

def Available (forest : TaggedForest C α ρ ι) (colors : List C) (wanted : ρ) : Prop :=
  ∃ q ∈ colors, ∃ current, forest q = some current ∧ Candidates current wanted

theorem scan (identifier : ρ → η) (color : α → C) (source : Cursor α ρ)
    (forest : TaggedForest C α ρ ι) (represented : ProjectionForest.Represents color source (erase forest))
    (physicalUnique : Unique forest) (logicalUnique : Distinguishes identifier source.tree)
    (wanted : ρ) (wantedInside : wanted ∈ source.tree.records) (colors : List C)
    (available : Available forest colors wanted) :
    ∃ reads cost, Run (program identifier (identifier wanted)) (.scan colors) (encode forest)
      (.found wanted) (encode forest) reads cost ∧ cost ≤ 5*colors.length := by
  induction colors with
  | nil => obtain ⟨q,member,_⟩ := available; simp only [List.not_mem_nil] at member
  | cons q rest ih =>
    obtain ⟨parentReads,parentCost,first,parentBound⟩ := parent_prefix identifier (identifier wanted) q rest forest physicalUnique
    cases parentHit : lookup identifier (identifier wanted) (parentEntries (forest q)) with
    | some actual =>
      have equal := lookup_sound identifier source.tree wanted wantedInside logicalUnique _
        (parent_inside color source forest represented q) actual parentHit
      subst actual
      rw [parentResult,parentHit] at first
      exact ⟨_,parentCost,first.run rfl,by simp only [List.length_cons]; omega⟩
    | none =>
      rw [parentResult,parentHit] at first
      obtain ⟨currentReads,second⟩ := current_prefix identifier (identifier wanted) q rest forest
      cases currentHit : lookup identifier (identifier wanted) (currentEntries (forest q)) with
      | some actual =>
        have equal := lookup_sound identifier source.tree wanted wantedInside logicalUnique _
          (current_inside color source forest represented q) actual currentHit
        subst actual
        rw [currentResult,currentHit] at second
        exact ⟨_,parentCost+1,(first.append second).run rfl,by simp only [List.length_cons]; omega⟩
      | none =>
        rw [currentResult,currentHit] at second
        have remaining : Available forest rest wanted := by
          obtain ⟨candidate,member,current,present,occurs⟩ := available
          by_cases equal : candidate = q
          · subst candidate
            exact False.elim (not_candidate identifier wanted current
              (by simpa only [present] using currentHit) (by simpa only [present] using parentHit) occurs)
          · exact ⟨candidate,(List.mem_cons.mp member).resolve_left equal,current,present,occurs⟩
        obtain ⟨lastReads,lastCost,tail,lastBound⟩ := ih remaining
        exact ⟨_,_,(first.append second).then_run tail,by simp only [List.length_cons]; omega⟩

theorem find [Fintype C] (identifier : ρ → η) (color : α → C) (source : Cursor α ρ)
    (forest : TaggedForest C α ρ ι) (represented : ProjectionForest.Represents color source (erase forest))
    (physicalUnique : Unique forest) (logicalUnique : Distinguishes identifier source.tree)
    (wanted : ρ) (available : ∃ q current, forest q = some current ∧ Candidates current wanted) :
    ∃ reads cost, Run (program identifier (identifier wanted)) (.scan (Finset.univ.sort (· ≤ ·))) (encode forest)
      (.found wanted) (encode forest) reads cost ∧ cost ≤ 5*Fintype.card C := by
  have wantedInside : wanted ∈ source.tree.records := by
    obtain ⟨q,current,present,candidate⟩ := available
    exact candidates_inside color source forest represented q current present wanted candidate
  have complete : Available forest (Finset.univ.sort (· ≤ ·)) wanted := by
    obtain ⟨q,current,present,candidate⟩ := available
    exact ⟨q,by simp,current,present,candidate⟩
  simpa only [Finset.length_sort,Finset.card_univ] using
    scan identifier color source forest represented physicalUnique logicalUnique wanted wantedInside _ complete

theorem find_current [Fintype C] (identifier : ρ → η) (color : α → C) (source : Cursor α ρ)
    (forest : TaggedForest C α ρ ι) (represented : ProjectionForest.Represents color source (erase forest))
    (physicalUnique : Unique forest) (logicalUnique : Distinguishes identifier source.tree) :
    ∃ reads cost, Run (program identifier (identifier source.focus.rootRecord))
      (.scan (Finset.univ.sort (· ≤ ·))) (encode forest) (.found source.focus.rootRecord)
      (encode forest) reads cost ∧ cost ≤ 5*Fintype.card C := by
  apply find identifier color source forest represented physicalUnique logicalUnique source.focus.rootRecord
  let q := source.focus.rootOwner color
  have inWhole : q ∈ source.tree.support color :=
    ProjectionForest.support_focus color source.focus source.ancestors (Source.rootOwner_mem color source.focus)
  have atRep := represented q
  cases present : forest q with
  | none =>
    simp only [erase,present,Option.map_none,ProjectionForest.RepresentsAt] at atRep
    exact False.elim (atRep inWhole)
  | some current =>
    simp only [erase,present,Option.map_some,ProjectionForest.RepresentsAt] at atRep
    obtain ⟨_,member,_⟩ := read_record color source atRep
    exact ⟨q,current,present,Or.inl (by simpa only [Cursor.mapRecords,Source.mapRecords_root] using member)⟩

theorem find_parent [Fintype C] (identifier : ρ → η) (color : α → C) (right : Bool)
    (l r : Source α ρ) (record : ρ) (outside) (forest : TaggedForest C α ρ ι)
    (represented : ProjectionForest.Represents color
      (if right then ⟨r,.right l record::outside⟩ else ⟨l,.left record r::outside⟩) (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : Distinguishes identifier (Cursor.tree ⟨.fork record l r,outside⟩)) :
    ∃ reads cost, Run (program identifier (identifier record)) (.scan (Finset.univ.sort (· ≤ ·))) (encode forest)
      (.found record) (encode forest) reads cost ∧ cost ≤ 5*Fintype.card C := by
  apply find identifier color _ forest represented physicalUnique
    (by cases right <;> exact logicalUnique) record
  exact PhysicalForestMetadata.parent_candidate color right l r record outside forest represented

end ChaCha.Paper20261030.PhysicalRecordFinder
