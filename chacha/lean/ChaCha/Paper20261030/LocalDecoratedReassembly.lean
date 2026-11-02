import ChaCha.Paper20261030.LocalContextReassembly
import ChaCha.Paper20261030.DecoratedContextReassembly

/-! Local reassembly including the record prefixes at exposed context
vertices. Prefix lengths and replacement prefixes are finite packet inputs.
Each edit reads the actual reached record list and preserves its suffix.
Acquiring the packets and validating their structural fields are separate
obligations; no subtree is an input to this instruction generator.
-/

namespace ChaCha.Paper20261030.OrderedContext.Local

open RouterProjection ColoredStorage SourcePointer ProjectionLocal LocalProjectedRotation
open LocalRecordActions (Action)

variable {ι α ρ : Type*}

theorem decorate_present (records : List ρ) (source : Projected α ρ) :
    (decorate records source).isSome = source.isSome := by
  cases source <;> rfl

theorem decorated_present (blocks : ι → Projected α ρ) (t : Source ι (List ρ)) :
    (decorated blocks t).isSome = present (fun key => (blocks key).isSome) t.shape := by
  induction t <;> simp_all only [decorated,decorate_present,join_isSome,Source.shape,present]

theorem remove_prefix (records : List ρ) (source : Projected α ρ) :
    Transforms [.drop records.length] (decorate records source) source 2 := by
  cases source with
  | none => trivial
  | some source =>
    intro outside
    have run := LocalRecordActions.drop records.length (source.setRoot (records++source.rootRecord)) outside
    have equal : (source.setRoot (records++source.rootRecord)).setRoot
        ((source.setRoot (records++source.rootRecord)).rootRecord.drop records.length) = source := by
      cases source <;> simp [Source.setRoot,Source.rootRecord]
    exact ⟨_,2,by simpa only [equal] using run,le_rfl⟩

theorem insert_prefix (records : List ρ) (source : Projected α ρ) :
    Transforms [.prepend records] source (decorate records source) 2 := by
  cases source with
  | none => trivial
  | some source => exact fun outside => ⟨_,2,LocalRecordActions.prepend records source outside,le_rfl⟩

def clear (bits : ι → Bool) : Source ι (List ρ) → List (Action ρ)
  | .leaf _ records => [.drop records.length]
  | .fork records l r =>
      ([.drop records.length] ++ liftLeft (present bits l.shape) (present bits r.shape) (clear bits l)) ++
        liftRight (present bits l.shape) (present bits r.shape) (clear bits r)

def install (bits : ι → Bool) : Source ι (List ρ) → List (Action ρ)
  | .leaf _ records => [.prepend records]
  | .fork records l r =>
      (liftLeft (present bits l.shape) (present bits r.shape) (install bits l) ++
        liftRight (present bits l.shape) (present bits r.shape) (install bits r)) ++ [.prepend records]

theorem clear_run (blocks : ι → Projected α ρ) (t : Source ι (List ρ)) :
    Transforms (clear (fun key => (blocks key).isSome) t)
      (decorated blocks t) (realize blocks t.shape) (6*vertices t) := by
  induction t with
  | leaf key records => exact (remove_prefix records (blocks key)).mono (by simp only [vertices]; omega)
  | fork records l r ihl ihr =>
    have actual := ((remove_prefix records _).trans (ihl.join_left (decorated blocks r))).trans
      (ihr.join_right (realize blocks l.shape))
    simpa only [clear,decorated,Source.shape,realize,decorated_present,realize_present] using
      actual.mono (by simp only [vertices]; omega)

theorem install_run (blocks : ι → Projected α ρ) (t : Source ι (List ρ)) :
    Transforms (install (fun key => (blocks key).isSome) t)
      (realize blocks t.shape) (decorated blocks t) (6*vertices t) := by
  induction t with
  | leaf key records => exact (insert_prefix records (blocks key)).mono (by simp only [vertices]; omega)
  | fork records l r ihl ihr =>
    have actual := ((ihl.join_left (realize blocks r.shape)).trans (ihr.join_right (decorated blocks l))).trans
      (insert_prefix records _)
    simpa only [install,decorated,Source.shape,realize,decorated_present,realize_present] using
      actual.mono (by simp only [vertices]; omega)

def decoratedActions (bits : ι → Bool) (before after : Source ι (List ρ)) : List (Action ρ) :=
  (clear bits before ++ reassemble bits before.shape after.shape) ++ install bits after

theorem decorated_run (blocks : ι → Projected α ρ) (before after : Source ι (List ρ))
    (ordered : before.shape.leaves = after.shape.leaves) :
    Transforms (decoratedActions (fun key => (blocks key).isSome) before after)
      (decorated blocks before) (decorated blocks after) (36*before.shape.leaves.length) := by
  have first := clear_run blocks before
  have middle := reassemble_run blocks before.shape after.shape (context_full before) (context_full after) ordered
  have last := install_run blocks after
  have nb := context_vertices before
  have na := context_vertices after
  have cb := Router.full_leaf_count before.shape (context_full before) (SourcePointer.source_nonempty before)
  have ca := Router.full_leaf_count after.shape (context_full after) (SourcePointer.source_nonempty after)
  rw [← ordered] at na ca
  exact ((first.trans middle).trans last).mono (by omega)

end ChaCha.Paper20261030.OrderedContext.Local
