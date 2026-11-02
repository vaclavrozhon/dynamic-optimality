import ChaCha.Paper20261030.MultiSourceValidity

set_option autoImplicit false

/-!
# Running a component controller while retaining extra physical fingers

The controller's registers occupy the left summand of a larger register
type. Extra registers may point anywhere in the tree. Ordinary rotation
transport keeps them on their physical vertices. The compiler changes
only register names, with exactly the same operations and observations.
-/

namespace ChaCha.Paper20261030.MultiSourceRegisterExtension

open ColoredStorage SourcePointer MultiSourceProgram

variable {α ρ F G σ : Type*} [DecidableEq F] [DecidableEq G]

def instruction : Instruction σ F ρ → Instruction σ (Sum F G) ρ
  | .halt => .halt
  | .read finger next => .read (.inl finger) next
  | .nav finger action next => .nav (.inl finger) action next
  | .write finger fresh next => .write (.inl finger) fresh next
  | .copy destination origin next => .copy (.inl destination) (.inl origin) next

def program (source : Program σ F ρ) : Program σ (Sum F G) ρ := fun state => instruction (source state)

def project (config : Configuration (Sum F G) α ρ) : Configuration F α ρ :=
  ⟨config.tree,fun finger => config.fingers (.inl finger)⟩

def observation (entry : F × ρ) : Sum F G × ρ := (.inl entry.1,entry.2)

theorem project_move (config : Configuration (Sum F G) α ρ) (finger : F)
    (action : DynamicOptimality.LocalProgram.Move) (before after : Cursor α ρ) :
    project (moveResult config (.inl finger) action before after) =
      moveResult (project config) finger action before after := by
  apply congrArg₂ Configuration.mk
  · rfl
  · funext other
    simp only [project,moveResult,Function.update_apply,Sum.inl.injEq]

theorem project_write (config : Configuration (Sum F G) α ρ) (current : Cursor α ρ) (fresh : ρ) :
    project (writeResult config current fresh) = writeResult (project config) current fresh := rfl

theorem project_copy (config : Configuration (Sum F G) α ρ) (destination origin : F) :
    project (copyResult config (.inl destination) (.inl origin)) = copyResult (project config) destination origin := by
  apply congrArg₂ Configuration.mk
  · rfl
  · funext other
    simp only [project,copyResult,Function.update_apply,Sum.inl.injEq]

theorem compile_step (source : Program σ F ρ) {state next : σ}
    {before after : Configuration F α ρ} {entry : Option (F × ρ)}
    (step : Step source state before next after entry)
    (global : Configuration (Sum F G) α ρ) (represented : project global = before) :
    ∃ target, Step (program source) state global next target (entry.map observation) ∧ project target = after := by
  have tree : global.tree = before.tree := congrArg Configuration.tree represented
  have finger : ∀ f, global.fingers (.inl f) = before.fingers f := fun f => congrArg (fun config => config.fingers f) represented
  cases step with
  | readNone code absent =>
    refine ⟨global,Step.readNone (congrArg instruction code) ?_,represented⟩
    exact (finger _).trans absent
  | readSome code present reached =>
    refine ⟨global,Step.readSome (congrArg instruction code) ((finger _).trans present) (by simpa only [tree] using reached),represented⟩
  | nav code present reached moved =>
    refine ⟨_,Step.nav (congrArg instruction code) ((finger _).trans present) (by simpa only [tree] using reached) moved,?_⟩
    rw [project_move,represented]
  | write code present reached =>
    refine ⟨_,Step.write (congrArg instruction code) ((finger _).trans present) (by simpa only [tree] using reached),?_⟩
    rw [project_write,represented]
  | copy code =>
    exact ⟨_,Step.copy (congrArg instruction code),by rw [project_copy,represented]⟩

theorem compile_run (source : Program σ F ρ) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (global : Configuration (Sum F G) α ρ) (represented : project global = before) :
    ∃ target, Run (program source) state global last target (reads.map observation) cost ∧ project target = after := by
  induction run generalizing global with
  | halt stopped => exact ⟨global,.halt (by simp only [program,stopped,instruction]),represented⟩
  | next first rest ih =>
    obtain ⟨middle,step,middleRep⟩ := compile_step source first global represented
    obtain ⟨target,body,targetRep⟩ := ih middle middleRep
    refine ⟨target,?_,targetRep⟩
    simpa only [List.map_append,Option.toList_map] using Run.next step body

theorem execute (source : Program σ F ρ) {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (global : Configuration (Sum F G) α ρ) (represented : project global = before) (valid : WellFormed global) :
    ∃ target, Run (program source) state global last target (reads.map observation) cost ∧
      project target = after ∧ WellFormed target := by
  obtain ⟨target,actual,finalRep⟩ := compile_run source run global represented
  exact ⟨target,actual,finalRep,actual.wellFormed valid⟩

end ChaCha.Paper20261030.MultiSourceRegisterExtension
