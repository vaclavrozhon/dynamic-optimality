import MultiSplay.ClassicalSwitchFrame
import MultiSplay.ClassicalSwitchAdmissible

/-! # Physical splaying of the state-determined classical forest word -/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder)
open ChaCha.Primary (Key)
open EndpointEncoding CommonForest

variable {α : Type*}

theorem selected_execution {state : State} {reference : RawTree α} {address : Key}
    {left right : RawTree α} {pivot : α}
    (found : referenceAt reference address = .node left pivot right)
    (whole incoming : RawTree α)
    (sourceKeys : inorder whole = inorder (sourceComponent state reference address))
    (incomingKeys : inorder incoming = inorder (incomingComponent state reference address))
    (unique : (inorder whole).Nodup) :
    ∃ after parked rotations,
      Execution pivot incoming (state address) (componentSpine state reference address).lower
        (componentSpine state reference address).upper whole after parked rotations ∧
      SplayTrace [whole,incoming] (eventWord reference state address) [after,parked]
        (rotations + 2 + 2*(componentSpine state reference address).lower.count +
          2*(componentSpine state reference address).upper.count) ∧
      inorder after = inorder (targetComponent state reference address) ∧
      inorder parked = inorder (oldComponent state reference address) := by
  have real : referenceAt reference address ≠ .empty := by simp [found]
  have path := selected_path state address real
  rw [found] at path
  have side : restrict state (address.take (startDepth state address))
      (address.drop (startDepth state address)) = state address := by
    rw [restrict_eq, List.take_append_drop]
  have current : restrict (restrict state (address.take (startDepth state address)))
      (address.drop (startDepth state address)) = restrict state address := by
    rw [← restrict_append, List.take_append_drop]
  obtain ⟨after,parked,rotations,run,trace,afterKeys,oldKeys⟩ := path.eventWord_execution whole incoming sourceKeys
    (by simpa only [incomingComponent, found, side, current] using incomingKeys) unique
  refine ⟨after,parked,rotations,?_,?_,afterKeys,?_⟩
  · simpa only [side] using run
  · simpa only [← eventWord_selected state address real] using trace
  · simpa only [oldComponent, found, side, current] using oldKeys

theorem eventWord_canSplay {state : State} {reference : RawTree α} {address : Key}
    (real : referenceAt reference address ≠ .empty)
    (unique : (inorder reference).Nodup) :
    ∀ event ∈ eventWord reference state address, event.CanSplay := by
  obtain ⟨remainder,before,_⟩ := selected_partition state reference address real
  have selectedUnique := ((forest_unique state unique).perm before).component
    (tree := sourceComponent state reference address) (by simp)
  have path := selected_path state address real
  cases focus : referenceAt reference address with
  | empty => exact False.elim (real focus)
  | node left pivot right =>
      rw [focus] at path
      have sourceEq := congrArg inorder path.before
      have side : restrict state (address.take (startDepth state address))
          (address.drop (startDepth state address)) = state address := by
        rw [restrict_eq, List.take_append_drop]
      have current : restrict (restrict state (address.take (startDepth state address)))
          (address.drop (startDepth state address)) = restrict state address := by
        rw [← restrict_append, List.take_append_drop]
      rw [Spine.before_inorder, side, current] at sourceEq
      have domainsUnique := sourceEq ▸ selectedUnique
      simpa only [eventWord, focus] using word_canSplay (state address)
        (componentSpine state reference address).lower (componentSpine state reference address).upper
        (inorder (tail (restrict state address) (state address) (.node left pivot right)))
        (inorder (tail (restrict state address) (!(state address)) (.node left pivot right))) pivot domainsUnique

theorem domain_append {a b c : List (List α)} {first rest : List (Event α)}
    (head : Domains.Trace a first b) (tail : Domains.Trace b rest c) :
    Domains.Trace a (first ++ rest) c := by
  induction head with
  | nil => simpa using tail
  | cons step remaining ih => simpa only [List.append_assoc] using Domains.Trace.cons step (ih tail)

theorem domain_context {a b : List (List α)} {word : List (Event α)}
    (run : Domains.Trace a word b) (front back : List (List α)) :
    Domains.Trace (front ++ a ++ back) word (front ++ b ++ back) := by
  induction run with
  | nil => exact .nil _
  | cons step rest ih => exact .cons (step.context front back) ih

theorem domain_reorder {a b : List (List α)} (order : a.Perm b) : Domains.Trace a [] b :=
  .cons (.reorder order) (.nil _)

/-- A switch has a real canonical domain execution. All untouched components
are framed by the derived canonical partition, not supplied as a hypothesis. -/
theorem switch_domains {state : State} {reference : RawTree α} {address : Key}
    (real : referenceAt reference address ≠ .empty) (unique : (inorder reference).Nodup) :
    Domains.Trace (domains (forest state reference)) (eventWord reference state address)
      (domains (forest (toggle state address) reference)) := by
  obtain ⟨remainder,before,after⟩ := selected_partition state reference address real
  have selectedUnique := ((forest_unique state unique).perm before).component
    (tree := sourceComponent state reference address) (by simp)
  cases found : referenceAt reference address with
  | empty => exact False.elim (real found)
  | node left pivot right =>
      obtain ⟨result,parked,rotations,_,run,resultKeys,oldKeys⟩ := selected_execution found
        (sourceComponent state reference address) (incomingComponent state reference address) rfl rfl selectedUnique
      have localRun := domain_context run.toDomains [] (domains remainder)
      have beforeRun := domain_reorder (before.map inorder)
      have afterRun := domain_reorder (after.map inorder).symm
      have middle : Domains.Trace (domains (sourceComponent state reference address :: incomingComponent state reference address :: remainder))
          (eventWord reference state address)
          (domains (targetComponent state reference address :: oldComponent state reference address :: remainder)) := by
        simpa [domains, resultKeys, oldKeys] using localRun
      simpa only [domains, List.nil_append, List.append_nil] using
        domain_append beforeRun (domain_append middle afterRun)

end MultiSplay.ClassicalSwitch
