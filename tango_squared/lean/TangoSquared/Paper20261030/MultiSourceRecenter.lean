import TangoSquared.Paper20261030.MultiSourceMask

/-! Charged recentering of a fixed register set at an already reached
vertex. Each copy costs one operation. The anchor remains unchanged even
if it also occurs in the destination list; no addresses are runtime data.
-/

namespace TangoSquared.Paper20261030.MultiSourceRecenter

open ColoredStorage MultiSourceProgram

variable {α ρ F : Type*} [DecidableEq F]

def program (origin : F) : Program (List F) F ρ
  | [] => .halt
  | destination::rest => .copy destination origin rest

def execute (origin : F) (config : Configuration F α ρ) : List F → Configuration F α ρ
  | [] => config
  | destination::rest => execute origin (copyResult config destination origin) rest

theorem run (origin : F) (config : Configuration F α ρ) (destinations : List F) :
    Run (program origin) destinations config [] (execute origin config destinations) [] destinations.length := by
  induction destinations generalizing config with
  | nil => exact .halt rfl
  | cons destination rest ih =>
    exact .next (program := program origin) (Step.copy (program := program origin) (state := destination::rest) rfl) (ih _)

theorem execute_tree (origin : F) (config : Configuration F α ρ) (destinations : List F) :
    (execute origin config destinations).tree = config.tree := by
  induction destinations generalizing config with
  | nil => rfl
  | cons destination rest ih => exact ih _

theorem execute_fingers (origin : F) (config : Configuration F α ρ) (destinations : List F) (finger : F) :
    (execute origin config destinations).fingers finger =
      if finger ∈ destinations then config.fingers origin else config.fingers finger := by
  induction destinations generalizing config with
  | nil => simp [execute]
  | cons destination rest ih =>
    simp only [execute,ih,copyResult]
    have anchor : Function.update config.fingers destination (config.fingers origin) origin = config.fingers origin := by
      by_cases same : origin = destination <;> simp [same]
    by_cases same : finger = destination
    · subst finger
      simp only [List.mem_cons_self,if_true,Function.update_self]
      by_cases member : destination ∈ rest
      · simp [member,anchor]
      · simp [member]
    · by_cases member : finger ∈ rest <;> simp [same,member,anchor]

theorem all_fingers (origin : F) (config : Configuration F α ρ) (destinations : List F)
    (covers : ∀ finger, finger ∈ destinations) :
    execute origin config destinations = ⟨config.tree,fun _ => config.fingers origin⟩ := by
  have tree := execute_tree origin config destinations
  have fingers : (execute origin config destinations).fingers = fun _ => config.fingers origin := by
    funext finger
    simp only [execute_fingers,covers finger,if_true]
  cases h : execute origin config destinations
  simp_all

def three : List (Option Bool) := [none,some true,some false]

theorem three_covers (finger : Option Bool) : finger ∈ three := by
  cases finger with
  | none => simp [three]
  | some side => cases side <;> simp [three]

theorem three_run (origin : Option Bool) (config : Configuration (Option Bool) α ρ) :
    Run (program origin) three config [] ⟨config.tree,fun _ => config.fingers origin⟩ [] 3 := by
  have actual := run origin config three
  rw [all_fingers origin config three three_covers] at actual
  exact actual

end TangoSquared.Paper20261030.MultiSourceRecenter
