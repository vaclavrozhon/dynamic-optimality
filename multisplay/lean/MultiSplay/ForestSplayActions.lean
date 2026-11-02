import MultiSplay.ForestUniqueness

/-! # A single physical forest event, independent of component-list order -/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder)

variable {α : Type*}

def Event.inputDomains : Event α → List (List α)
  | .search keys _ => [keys]
  | .split left pivot right => [left ++ [pivot] ++ right]
  | .join left _ right => [left, right]

inductive SplayPrimitive : Event α → List (RawTree α) → List (RawTree α) → Nat → Prop
  | search {key : α} {before after : RawTree α} {cost : Nat}
      (execution : Auxiliary.Splay key before after cost) :
      SplayPrimitive (.search (inorder before) key) [before] [after] (cost+1)
  | split {pivot : α} {before left right : RawTree α} {cost : Nat}
      (execution : Auxiliary.Splay pivot before (.node left pivot right) cost) :
      SplayPrimitive (.split (inorder left) pivot (inorder right)) [before] [left,right] (cost+1)
  | join (left right : RawTree α) (pivot : α) :
      SplayPrimitive (.join (inorder left) pivot (inorder right)) [left,right] [.node left pivot right] 1

theorem SplayPrimitive.domains {event : Event α} {before after : List (RawTree α)} {cost : Nat}
    (primitive : SplayPrimitive event before after cost) : before.map inorder = event.inputDomains := by
  cases primitive with
  | search | join => rfl
  | split execution => simpa only [List.map_cons, List.map_nil, Event.inputDomains, inorder] using congrArg (fun keys => [keys]) execution.inorder_eq

theorem SplayPrimitive.deterministic_of_eq {event event' : Event α} {before before' a b : List (RawTree α)} {x y : Nat}
    (first : SplayPrimitive event before a x) (second : SplayPrimitive event' before' b y)
    (sameEvent : event = event') (sameBefore : before = before')
    (unique : ∀ tree ∈ before, (inorder tree).Nodup) : a = b ∧ x = y := by
  cases first with
  | search execution =>
      cases second with
      | search other =>
          have keys := (Event.search.inj sameEvent).2
          have trees := (List.cons.inj sameBefore).1
          cases keys
          cases trees
          obtain ⟨rfl,rfl⟩ := execution.deterministic other (unique _ (by simp))
          exact ⟨rfl,rfl⟩
      | split | join => cases sameEvent
  | split execution =>
      cases second with
      | split other =>
          have keys := (Event.split.inj sameEvent).2.1
          have trees := (List.cons.inj sameBefore).1
          cases keys
          cases trees
          obtain ⟨same,rfl⟩ := execution.deterministic other (unique _ (by simp))
          obtain ⟨rfl,_,rfl⟩ := ChaCha.MTR.Tree.node.inj same
          exact ⟨rfl,rfl⟩
      | search | join => cases sameEvent
  | join left right pivot =>
      cases second with
      | join otherLeft otherRight otherPivot =>
          have keys := (Event.join.inj sameEvent).2.1
          have leftEq := (List.cons.inj sameBefore).1
          have rightEq := (List.cons.inj (List.cons.inj sameBefore).2).1
          cases keys
          cases leftEq
          cases rightEq
          exact ⟨rfl,rfl⟩
      | search | split => cases sameEvent

theorem SplayPrimitive.deterministic {event : Event α} {before a b : List (RawTree α)} {x y : Nat}
    (first : SplayPrimitive event before a x) (second : SplayPrimitive event before b y)
    (unique : ∀ tree ∈ before, (inorder tree).Nodup) : a = b ∧ x = y :=
  first.deterministic_of_eq second rfl rfl unique

def SplayAction (event : Event α) (before after : List (RawTree α)) (cost : Nat) : Prop :=
  ∃ selected returned context, SplayPrimitive event selected returned cost ∧
    before.Perm (selected++context) ∧ after.Perm (returned++context)

theorem SplayAction.deterministic {event : Event α} {a a' b b' : List (RawTree α)} {x y : Nat}
    (first : SplayAction event a b x) (second : SplayAction event a' b' y)
    (unique : UniqueKeys a) (same : a.Perm a') : b.Perm b' ∧ x = y := by
  obtain ⟨selected, returned, context, primitive, before, after⟩ := first
  obtain ⟨selected', returned', context', primitive', before', after'⟩ := second
  obtain ⟨rfl, contexts⟩ := unique.cancel_selection before (same.trans before')
    (primitive.domains.trans primitive'.domains.symm)
  obtain ⟨rfl, work⟩ := primitive.deterministic primitive'
    (fun tree member => unique.component (before.mem_iff.mpr (List.mem_append_left _ member)))
  exact ⟨after.trans ((contexts.append_left _).trans after'.symm), work⟩

theorem SplayAction.permute {event : Event α} {a a' b b' : List (RawTree α)} {cost : Nat}
    (action : SplayAction event a b cost) (before : a'.Perm a) (after : b'.Perm b) :
    SplayAction event a' b' cost := by
  obtain ⟨selected, returned, context, primitive, first, last⟩ := action
  exact ⟨selected, returned, context, primitive, before.trans first, after.trans last⟩

theorem SplayAction.context {event : Event α} {a b : List (RawTree α)} {cost : Nat}
    (action : SplayAction event a b cost) (front back : List (RawTree α)) :
    SplayAction event (front++a++back) (front++b++back) cost := by
  obtain ⟨selected, returned, context, primitive, first, last⟩ := action
  have lift : ∀ (forest part : List (RawTree α)), forest.Perm (part++context) →
      (front++forest++back).Perm (part++(context++back++front)) := by
    intro forest part order
    have cycle : (front++forest++back).Perm ((forest++back)++front) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm : (front++(forest++back)).Perm ((forest++back)++front))
    exact cycle.trans (by simpa only [List.append_assoc] using (order.append_right back).append_right front)
  exact ⟨selected, returned, context++back++front, primitive, lift _ _ first, lift _ _ last⟩

end MultiSplay.CommonForest
