import ChaCha.Paper20261030.ThreeColorConfiguration
import ChaCha.Paper20261030.MultiSourceDownward

/-! Charged setup of the three component fingers. The two presence bits
determine a schedule of at most five downward moves. Initially each used
finger is at the component root and each unused register is absent.
Acquiring the presence bits and recentering registers when entering from
another component belong to the primary controller.
-/

namespace ChaCha.Paper20261030.ForestConnector.ThreeColors

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ : Type*}

def entrySchedule (left right : Bool) : MultiSourceDownward.Schedule (Option Bool) :=
  (if right then [(none,false)] else []) ++
  (if left then [(none,true)] else []) ++
  (if left then (if right then [(some true,false)] else []) ++ [(some true,false)] else []) ++
  (if right then [(some false,true)] else [])

theorem entrySchedule_bound (left right : Bool) : (entrySchedule left right).length ≤ 5 := by
  cases left <;> cases right <;> decide

def entryConfiguration (forest : ProjectionForest.State (Option Bool) α ρ) (header : Source α (List ρ)) :
    Configuration (Option Bool) α (List ρ) :=
  ⟨(configuration forest ⟨header,[]⟩).tree,
    fun q => if q = none then some [] else if (forest q).isSome then some [] else none⟩

theorem entry_execute (forest : ProjectionForest.State (Option Bool) α ρ) (header : Source α (List ρ))
    (rooted : ∀ q current, forest q = some current → current.ancestors = []) :
    MultiSourceDownward.execute (entryConfiguration forest header)
      (entrySchedule (forest (some true)).isSome (forest (some false)).isSome) =
      some (configuration forest ⟨header,[]⟩) := by
  have rootMap : ∀ q, (forest q).map Cursor.ancestors = (forest q).map (fun _ => []) := by
    intro q
    cases present : forest q with
    | none => rfl
    | some current => simpa only [Option.map_some] using congrArg some (rooted q current present)
  cases left : forest (some true) <;> cases right : forest (some false)
  all_goals
    have leftRoot := rootMap (some true)
    have rightRoot := rootMap (some false)
    simp only [left,right,Option.map_some,Option.map_none,Option.some.injEq] at leftRoot rightRoot
    simp [entryConfiguration,configuration,left,right,entrySchedule,leftRoot,rightRoot,
      MultiSourceDownward.execute,MultiSourceProgram.join,single,Cursor.tree,plug,
      Function.update_apply,locate,descend,SourceLocalProgram.navigate,moveResult,transport,address,direction]
    funext q
    cases q with
    | none => simp
    | some side => cases side <;> simp [left,right,leftRoot,rightRoot]

theorem entry_run (forest : ProjectionForest.State (Option Bool) α ρ) (header : Source α (List ρ))
    (rooted : ∀ q current, forest q = some current → current.ancestors = []) :
    ∃ cost, Run MultiSourceDownward.program
      (entrySchedule (forest (some true)).isSome (forest (some false)).isSome)
      (entryConfiguration forest header) [] (configuration forest ⟨header,[]⟩) [] cost ∧ cost ≤ 5 :=
  ⟨_,MultiSourceDownward.execute_run _ _ _ (entry_execute forest header rooted),entrySchedule_bound _ _⟩

end ChaCha.Paper20261030.ForestConnector.ThreeColors
