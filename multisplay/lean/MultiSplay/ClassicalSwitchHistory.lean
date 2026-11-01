import MultiSplay.ClassicalSwitchForest

/-!
# Chronological realization of the classical MultiSplay word

Every switch reads the preference state left by the previous switch. The
resulting domain trace starts and ends at the actual canonical partitions.
Realization from any forest with those domains keeps the returned tree shapes
throughout the execution; it does not replace them by canonical shapes.
-/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder)
open TangoSquared.Primary (Key)
open EndpointEncoding CommonForest

variable {α : Type*}

theorem schedule_domains (reference : RawTree α) (state : State) (owners : List Key)
    (unique : (inorder reference).Nodup)
    (real : ∀ owner ∈ owners, referenceAt reference owner ≠ .empty) :
    Domains.Trace (domains (forest state reference))
      ((schedule state owners).flatMap fun entry => eventWord reference entry.1 entry.2)
      (domains (forest (applySwitches state owners) reference)) := by
  induction owners generalizing state with
  | nil => exact .nil _
  | cons owner rest ih =>
      simpa only [schedule, List.flatMap_cons, applySwitches] using
        domain_append (switch_domains (state := state) (real owner (by simp)) unique)
          (ih (toggle state owner) (fun next member => real next (by simp [member])))

theorem schedule_canSplay (reference : RawTree α) (state : State) (owners : List Key)
    (unique : (inorder reference).Nodup)
    (real : ∀ owner ∈ owners, referenceAt reference owner ≠ .empty) :
    ∀ event ∈ (schedule state owners).flatMap
      (fun entry => eventWord reference entry.1 entry.2), event.CanSplay := by
  induction owners generalizing state with
  | nil => simp [schedule]
  | cons owner rest ih =>
      intro event member
      simp only [schedule, List.flatMap_cons, List.mem_append] at member
      rcases member with head | tail
      · exact eventWord_canSplay (real owner (by simp)) unique event head
      · exact ih (toggle state owner) (fun next inRest => real next (by simp [inRest])) event tail

theorem request_domains {reference : RawTree α} (state : State) (address : Key)
    (unique : (inorder reference).Nodup) (real : referenceAt reference address ≠ .empty) :
    Domains.Trace (domains (forest state reference)) (requestWord reference state address)
      (domains (forest (nodeStep state address) reference)) := by
  rw [← actualEmissions_state]
  apply schedule_domains reference state _ unique
  intro owner member
  exact referenceAt_prefix_nonempty real
    (ascendingEmissions_prefix ((actualEmissions_perm state address).mem_iff.mp member))

theorem request_canSplay {reference : RawTree α} (state : State) (address : Key)
    (unique : (inorder reference).Nodup) (real : referenceAt reference address ≠ .empty) :
    ∀ event ∈ requestWord reference state address, event.CanSplay := by
  apply schedule_canSplay reference state _ unique
  intro owner member
  exact referenceAt_prefix_nonempty real
    (ascendingEmissions_prefix ((actualEmissions_perm state address).mem_iff.mp member))

theorem history_domains (reference : RawTree α) (state : State) (addresses : List Key)
    (unique : (inorder reference).Nodup)
    (real : ∀ address ∈ addresses, referenceAt reference address ≠ .empty) :
    Domains.Trace (domains (forest state reference)) (historyWord reference state addresses)
      (domains (forest (addresses.foldl nodeStep state) reference)) := by
  induction addresses generalizing state with
  | nil => exact .nil _
  | cons address rest ih =>
      exact domain_append (request_domains state address unique (real address (by simp)))
        (ih (nodeStep state address) (fun next member => real next (by simp [member])))

theorem history_canSplay (reference : RawTree α) (state : State) (addresses : List Key)
    (unique : (inorder reference).Nodup)
    (real : ∀ address ∈ addresses, referenceAt reference address ≠ .empty) :
    ∀ event ∈ historyWord reference state addresses, event.CanSplay := by
  induction addresses generalizing state with
  | nil => simp [historyWord]
  | cons address rest ih =>
      intro event member
      simp only [historyWord, List.mem_append] at member
      rcases member with head | tail
      · exact request_canSplay state address unique (real address (by simp)) event head
      · exact ih (nodeStep state address) (fun next inRest => real next (by simp [inRest])) event tail

/-- The entire request history has an actual pointer-backed splay realization
from the supplied initial forest. Only its ordered domains are prescribed. -/
theorem history_realize (reference : RawTree α) (state : State) (addresses : List Key)
    (unique : (inorder reference).Nodup)
    (real : ∀ address ∈ addresses, referenceAt reference address ≠ .empty)
    {initial : List (RawTree α)} (same : domains initial = domains (forest state reference)) :
    ∃ final work, PointerSplayTrace initial (historyWord reference state addresses) final work ∧
      domains final = domains (forest (addresses.foldl nodeStep state) reference) :=
  (history_domains reference state addresses unique real).realize
    (history_canSplay reference state addresses unique real) same

theorem request_realize {reference : RawTree α} (state : State) (address : Key)
    (unique : (inorder reference).Nodup) (real : referenceAt reference address ≠ .empty)
    {initial : List (RawTree α)} (same : domains initial = domains (forest state reference)) :
    ∃ final work, PointerSplayTrace initial (requestWord reference state address) final work ∧
      domains final = domains (forest (nodeStep state address) reference) :=
  (request_domains state address unique real).realize
    (request_canSplay state address unique real) same

end MultiSplay.ClassicalSwitch
