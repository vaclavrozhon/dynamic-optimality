import ChaCha.Paper20261030.LocalHeadReassembly
import ChaCha.Paper20261030.ExposedHeadReassembly

/-! Explicit finite contexts for the manuscript's actual exposed views.
The nine active/dormant record prefixes determine the command list without
choosing a context from an existential trace theorem.
-/

namespace ChaCha.Paper20261030.HeadBlocks.ExposedLocal

open ColoredStorage ProjectionLocal OrderedContext LocalProjectedRotation

variable {α ρ : Type*}

def decorateContext (records : List ρ) (context : Source (Fin 8) (List ρ)) : Source (Fin 8) (List ρ) :=
  context.setRoot (records++context.rootRecord)

private def leaf (key : Fin 8) : Source (Fin 8) (List ρ) := .leaf key []
private def join (left right : Source (Fin 8) (List ρ)) : Source (Fin 8) (List ρ) := .fork [] left right

def dormantContext (l b r : Fin 8) (records : DormantRecords ρ) : Source (Fin 8) (List ρ) :=
  join (join (decorateContext records.left (leaf l)) (decorateContext records.bottom (leaf b)))
    (decorateContext records.right (leaf r))

def activeContext (l r tl b tr : Fin 8) (boundary : Source (Fin 8) (List ρ))
    (direction : Bool) (records : ActiveRecords ρ) : Source (Fin 8) (List ρ) :=
  let child := decorateContext records.attachment boundary
  let left := if direction then join child (leaf tl) else leaf tl
  let right := if direction then leaf tr else join (leaf tr) child
  join (join
    (decorateContext records.lowerLeft (join (leaf l) (decorateContext records.upperLeft left)))
    (decorateContext records.bottom (leaf b)))
    (decorateContext records.lowerRight (join (decorateContext records.upperRight right) (leaf r)))

def beforeContext (direction : Bool) (active : ActiveRecords ρ) (dormant : DormantRecords ρ) : Source (Fin 8) (List ρ) :=
  activeContext 0 7 1 2 3 (dormantContext 4 5 6 dormant) direction active

def afterContext (direction : Bool) (active : ActiveRecords ρ) (dormant : DormantRecords ρ) : Source (Fin 8) (List ρ) :=
  activeContext 0 7 4 5 6 (dormantContext 1 2 3 dormant) (!direction) active

theorem decorateContext_realize (blocks : Fin 8 → Projected α ρ) (records : List ρ)
    (context : Source (Fin 8) (List ρ)) :
    decorated blocks (decorateContext records context) = decorate records (decorated blocks context) := by
  cases context <;> exact OrderedContext.decorate_append _ _ _

theorem dormant_realize (blocks : Fin 8 → Projected α ρ) (l b r : Fin 8) (records : DormantRecords ρ) :
    decorated blocks (dormantContext l b r records) = dormantView (blocks l) (blocks b) (blocks r) records := by
  simp only [dormantContext,join,decorated,decorateContext_realize,leaf,decorate_nil,dormantView]

theorem active_realize (blocks : Fin 8 → Projected α ρ) (l r tl b tr : Fin 8)
    (boundary : Source (Fin 8) (List ρ)) (direction : Bool) (records : ActiveRecords ρ) :
    decorated blocks (activeContext l r tl b tr boundary direction records) =
      activeView (blocks l) (blocks r) (blocks tl) (blocks b) (blocks tr) (decorated blocks boundary) direction records := by
  cases direction <;> simp only [activeContext,activeView,Bool.false_eq_true,if_false,if_true,
    join,decorated,decorateContext_realize,leaf,decorate_nil]

theorem before_realize (blocks : Fin 8 → Projected α ρ) (direction : Bool)
    (active : ActiveRecords ρ) (dormant : DormantRecords ρ) :
    decorated blocks (beforeContext direction active dormant) = exposedBefore blocks direction active dormant := by
  simp only [beforeContext,active_realize,dormant_realize,exposedBefore]

theorem after_realize (blocks : Fin 8 → Projected α ρ) (direction : Bool)
    (active : ActiveRecords ρ) (dormant : DormantRecords ρ) :
    decorated blocks (afterContext direction active dormant) = exposedAfter blocks direction active dormant := by
  simp only [afterContext,active_realize,dormant_realize,exposedAfter]

theorem before_shape (direction : Bool) (active : ActiveRecords ρ) (dormant : DormantRecords ρ) :
    (beforeContext direction active dormant).shape = (before direction).shape := by
  cases direction <;> rfl

theorem after_shape (direction : Bool) (active : ActiveRecords ρ) (dormant : DormantRecords ρ) :
    (afterContext direction active dormant).shape = (after direction).shape := by
  cases direction <;> rfl

def actions (direction : Bool) (bits : Fin 8 → Bool)
    (oldActive newActive : ActiveRecords ρ) (oldDormant newDormant : DormantRecords ρ) : List (LocalRecordActions.Action ρ) :=
  OrderedContext.Local.decoratedActions bits (beforeContext direction oldActive oldDormant)
    (afterContext direction newActive newDormant)

theorem reassemble (blocks : Fin 8 → Projected α ρ) (direction : Bool)
    (oldActive newActive : ActiveRecords ρ) (oldDormant newDormant : DormantRecords ρ) :
    Transforms (actions direction (fun key => (blocks key).isSome) oldActive newActive oldDormant newDormant)
      (exposedBefore blocks direction oldActive oldDormant)
      (exposedAfter blocks direction newActive newDormant) 288 := by
  have actual := OrderedContext.Local.decorated_run blocks (beforeContext direction oldActive oldDormant)
    (afterContext direction newActive newDormant)
    (by rw [before_shape,after_shape]; exact block_order direction)
  simpa only [actions,before_realize,after_realize,before_shape,block_count,Nat.reduceMul] using actual

end ChaCha.Paper20261030.HeadBlocks.ExposedLocal
