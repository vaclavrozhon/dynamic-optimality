import MultiSplay.GlobalPreferredExecution
import MultiSplay.GlobalClassicalAccess

/-! # Physical switch histories and the mandatory final root switch -/

namespace MultiSplay.Global.Preferred

open DynamicOptimality DynamicOptimality.SearchRotation
open ChaCha.MTR
open Pointer (MarkedTree)
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch CommonForest

variable {α : Type*}

/-- The selected pair's pure replay has the exact global event word even
when its physical component lies beneath several opaque attachments. -/
theorem Switch.local_trace {state : State} {reference before after : RawTree α}
    {address : Key} {count work : Nat}
    (run : Switch state reference address before after count work)
    (real : referenceAt reference address ≠ .empty) :
    ∃ source incoming target parked : RawTree α,
      SplayTrace [source,incoming] (eventWord reference state address) [target,parked] work := by
  induction run with
  | root path represented foreignRep mainRep oldRep attached execution partition actual trace => exact ⟨_,_,_,_,trace⟩
  | @inside state reference entry suffix before replacement count work index context
      represented found shape position child ih =>
      have member := List.mem_of_getElem? found
      have childReal : referenceAt entry.2 suffix ≠ .empty := by
        rw [← preferredHoles_referenceAt state reference member, ← referenceAt_append]
        exact real
      obtain ⟨source,incoming,target,parked,trace⟩ := ih childReal
      refine ⟨source,incoming,target,parked,?_⟩
      rw [eventWord_hole state reference member suffix real]
      exact trace

/-- A switch whose owner lies on the root preferred path ends with that
owner at the actual global BST root. -/
theorem Switch.root_of_follows {state : State} {reference before after : RawTree α}
    {address : Key} {count work : Nat}
    (run : Switch state reference address before after count work)
    (follows : RootPreferred state address)
    (real : referenceAt reference address ≠ .empty) :
    after.rootKey = (referenceAt reference address).rootKey := by
  cases run with
  | root path represented foreignRep mainRep oldRep attached execution partition actual trace =>
      rw [path.referenceAt]
      exact marked_erase_root execution.root
  | inside context represented found shape position child =>
      exact False.elim ((hole_owner_nonroot _ _ (List.mem_of_getElem? found) _ real)
        ((startDepth_zero _ _).mpr follows))

/-- The actual chronological switch sequence, retaining its evolving
preference state and both exact physical endpoints. -/
inductive Switches : State → RawTree α → List Key → RawTree α → RawTree α → Nat → Nat → Prop
  | nil (state : State) (reference physical : RawTree α) :
      Switches state reference [] physical physical 0 0
  | cons {state : State} {reference before middle after : RawTree α}
      {address : Key} {rest : List Key} {firstCount restCount firstWork restWork : Nat}
      (first : Switch state reference address before middle firstCount firstWork)
      (later : Switches (toggle state address) reference rest middle after restCount restWork) :
      Switches state reference (address::rest) before after
        (firstCount+restCount) (firstWork+restWork)

theorem Switches.rotations {state : State} {reference before after : RawTree α}
    {addresses : List Key} {count work : Nat}
    (run : Switches state reference addresses before after count work) :
    Rotations before after count := by
  induction run with
  | nil => exact .refl _
  | cons first later ih => exact first.rotations.append ih

theorem Switches.rotations_le_work {state : State} {reference before after : RawTree α}
    {addresses : List Key} {count work : Nat}
    (run : Switches state reference addresses before after count work) : count ≤ work := by
  induction run with
  | nil => rfl
  | cons first later ih => exact Nat.add_le_add first.rotations_le_work ih

theorem Switches.append {state : State} {reference before middle after : RawTree α}
    {first rest : List Key} {firstCount restCount firstWork restWork : Nat}
    (earlier : Switches state reference first before middle firstCount firstWork)
    (suffix : Switches (applySwitches state first) reference rest middle after restCount restWork) :
    Switches state reference (first++rest) before after
      (firstCount+restCount) (firstWork+restWork) := by
  induction earlier with
  | nil => simpa only [applySwitches, List.nil_append, Nat.zero_add] using suffix
  | cons first later ih =>
      simpa only [List.cons_append, Nat.add_assoc] using .cons first (ih suffix)

/-- Existence is proved on the actual evolving tree, not separately for
independent component domains. -/
theorem switches_exists (state : State) (reference physical : RawTree α) (addresses : List Key)
    (unique : reference.inorder.Nodup)
    (real : ∀ address ∈ addresses, referenceAt reference address ≠ .empty)
    (represented : Realizes state reference physical) :
    ∃ after count work, Switches state reference addresses physical after count work ∧
      Realizes (applySwitches state addresses) reference after := by
  induction addresses generalizing state physical with
  | nil => exact ⟨physical,0,0,.nil _ _ _,represented⟩
  | cons address rest ih =>
      obtain ⟨middle,firstCount,firstWork,first,next⟩ :=
        switch_exists state reference physical address unique (real _ (by simp)) represented
      obtain ⟨after,restCount,restWork,later,last⟩ :=
        ih (toggle state address) middle (fun owner member => real owner (by simp [member])) next
      exact ⟨after,firstCount+restCount,firstWork+restWork,.cons first later,last⟩

/-- The actual bottom-up ancestor switches followed by the mandatory final
switch bring the requested reference key to the global physical root. -/
theorem request_exists {n : Nat} (reference : BST 0 n) (key : Fin n)
    (state : State) (physical : RawTree Nat)
    (represented : Realizes state reference.toRaw physical) :
    ∃ after count work,
      Switches state reference.toRaw (actualEmissions state (nodeAddress reference key.val))
        physical after count work ∧
      Realizes (nodeStep state (nodeAddress reference key.val)) reference.toRaw after ∧
      after.rootKey = some key.val := by
  let address := nodeAddress reference key.val
  have unique : reference.toRaw.inorder.Nodup := reference.toRaw_ordered.imp (fun h => Nat.ne_of_lt h)
  obtain ⟨left,right,located⟩ := referenceAt_nodeAddress reference (Nat.zero_le _) key.isLt
  have real : referenceAt reference.toRaw address ≠ .empty := by simp [address,located]
  have prefixReal : ∀ owner ∈ (ancestorEmissions state address).reverse,
      referenceAt reference.toRaw owner ≠ .empty := by
    intro owner member
    apply actualEmissions_real reference (Nat.zero_le _) key.isLt state
    exact List.mem_append_left _ member
  obtain ⟨middle,firstCount,firstWork,earlier,next⟩ :=
    switches_exists state reference.toRaw physical (ancestorEmissions state address).reverse
      unique prefixReal represented
  obtain ⟨after,lastCount,lastWork,last,lastRep⟩ :=
    switch_exists (beforeFinal state address) reference.toRaw middle address unique real next
  have root := last.root_of_follows (beforeFinal_rootPreferred state address) real
  have final : Switches (beforeFinal state address) reference.toRaw [address] middle after
      lastCount lastWork := by
    simpa using Switches.cons last (Switches.nil _ _ _)
  refine ⟨after,firstCount+lastCount,firstWork+lastWork,earlier.append final,?_,?_⟩
  · simpa only [final_toggle] using lastRep
  · simpa only [address, located, Tree.rootKey] using root

/-- Searching the original physical BST is charged before any rotations.
The mandatory final switch pays its initial depth, so one request costs at
most twice its pure classical replay work plus one. -/
theorem request_access {n : Nat} (reference before : BST 0 n) (key : Fin n)
    (state : State) (represented : Realizes state reference.toRaw before.toRaw) :
    ∃ after count work,
      Switches state reference.toRaw (actualEmissions state (nodeAddress reference key.val))
        before.toRaw after count work ∧
      Realizes (nodeStep state (nodeAddress reference key.val)) reference.toRaw after ∧
      Access key.val before.toRaw after (before.depth key.val + 1 + count) ∧
      before.depth key.val + 1 + count ≤ 2*work+1 := by
  obtain ⟨after,count,work,run,next,root⟩ := request_exists reference key state before.toRaw represented
  obtain ⟨access,bound⟩ := rooted_access before key run.rotations root
  refine ⟨after,count,work,run,next,access,?_⟩
  have cost := run.rotations_le_work
  omega

end MultiSplay.Global.Preferred
