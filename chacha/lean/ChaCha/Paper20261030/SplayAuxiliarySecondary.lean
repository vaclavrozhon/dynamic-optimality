import ChaCha.Paper20261030.SplayAuxiliaryPreferred
import ChaCha.Paper20261030.DepthPreferences

/-!
# Secondary accesses with ordinary splay preferred-path auxiliaries

The depth reference is represented by the shared indexed BST on its actual
internal cuts. The preference state is exactly the existing decoded
secondary tree. Each first-wrong-edge step is a genuine classical root-path
repair, and the complete access telescopes one persistent forest potential.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree BST)
open DynamicOptimality.SearchRotation
open PreferredProjection
open MultiSplay EndpointEncoding ClassicalSwitch Global.Preferred

/-- The actual cut identities of a leaf-oriented depth reference. -/
def separatorReference : {a b : Nat} → DepthTree a b → BST a b
  | _,_,.leaf a => .empty a
  | _,_,.node _ _ _ left right => .node (separatorReference left) (separatorReference right)

@[simp] theorem separatorReference_height {a b : Nat} (reference : DepthTree a b) :
    (separatorReference reference).height = (LocalReferences.depthReference reference).height := by
  induction reference <;>
    simp_all [separatorReference,Splay.Tree.BST.height,LocalReferences.depthReference,
      RouterProjection.Router.height]

/-- Address-indexed preference bits; absent owners have the fixed value false. -/
def routerState {α : Type*} : PrefRouter α → State
  | .leaf _,_ => false
  | .fork bit _ _,[] => bit
  | .fork _ left _,false::rest => routerState left rest
  | .fork _ _ right,true::rest => routerState right rest

@[simp] theorem routerState_below_left {α : Type*} (bit : Bool) (left right : PrefRouter α) :
    below (routerState (.fork bit left right)) false = routerState left := rfl

@[simp] theorem routerState_below_right {α : Type*} (bit : Bool) (left right : PrefRouter α) :
    below (routerState (.fork bit left right)) true = routerState right := rfl

theorem head_erase {α : Type*} {request : α} {depth : Nat} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep request depth before after) : before.erase = after.erase := by
  induction step <;> simp_all [PrefRouter.erase]

private theorem toggle_fork_root {α : Type*} (bit : Bool) (left right : PrefRouter α) :
    routerState (.fork (!bit) left right) = toggle (routerState (.fork bit left right)) [] := by
  funext owner
  cases owner with
  | nil => simp [routerState,toggle]
  | cons side rest => cases side <;> simp [routerState,toggle]

private theorem toggle_fork_left {α : Type*} (bit : Bool) (left after right : PrefRouter α)
    (address : ChaCha.Primary.Key) (same : routerState after = toggle (routerState left) address) :
    routerState (.fork bit after right) = toggle (routerState (.fork bit left right)) (false::address) := by
  funext owner
  cases owner with
  | nil => simp [routerState,toggle]
  | cons side rest =>
      cases side <;> simp [routerState,toggle,List.cons.injEq]
      exact congrFun same rest

private theorem toggle_fork_right {α : Type*} (bit : Bool) (left right after : PrefRouter α)
    (address : ChaCha.Primary.Key) (same : routerState after = toggle (routerState right) address) :
    routerState (.fork bit left after) = toggle (routerState (.fork bit left right)) (true::address) := by
  funext owner
  cases owner with
  | nil => simp [routerState,toggle]
  | cons side rest =>
      cases side <;> simp [routerState,toggle,List.cons.injEq]
      exact congrFun same rest

/-- The already-counted abstract head step identifies the exact real pivot
and its preferred ancestor spine in the same static secondary reference. -/
theorem secondary_head_path {a b : Nat} (reference : DepthTree a b)
    {request depth : Nat} {before after : PrefRouter Nat}
    (shape : before.erase = LocalReferences.depthReference reference)
    (step : PrefRouter.HeadStep request depth before after) :
    ∃ address spine left pivot right,
      Path (routerState before) (separatorReference reference).toRaw address spine
        (.node left pivot right) ∧
      routerState after = toggle (routerState before) address := by
  induction reference generalizing before after depth with
  | leaf a =>
      cases before with
      | leaf value => cases step
      | fork bit left right => simp [PrefRouter.erase,LocalReferences.depthReference] at shape
  | @node a b cut ha hb left right ihl ihr =>
      cases before with
      | leaf value => simp [PrefRouter.erase,LocalReferences.depthReference] at shape
      | fork bit l r =>
          have shapes := RouterProjection.Router.fork.inj shape
          cases step with
          | leftRoot _ _ member =>
              exact ⟨[],[],_,cut,_,.here _ _,toggle_fork_root true l r⟩
          | rightRoot _ _ absent member =>
              exact ⟨[],[],_,cut,_,.here _ _,toggle_fork_root false l r⟩
          | @leftDown depth l l' r step =>
              obtain ⟨address,spine,x,pivot,y,path,same⟩ := ihl shapes.1 step
              refine ⟨false::address,spine++[(false,cut)],x,pivot,y,?_,?_⟩
              · exact .left rfl path
              · exact toggle_fork_left false l l' r address same
          | @rightDown depth r r' l absent step =>
              obtain ⟨address,spine,x,pivot,y,path,same⟩ := ihr shapes.2 step
              refine ⟨true::address,spine++[(true,cut)],x,pivot,y,?_,?_⟩
              · exact .right rfl path
              · exact toggle_fork_right true l r r' address same

/-- One actual secondary flip, with the same globally retained inventory. -/
theorem secondary_head_repair {a b : Nat} (reference : DepthTree a b)
    {request depth : Nat} {before after : PrefRouter Nat}
    (shape : before.erase = LocalReferences.depthReference reference)
    (step : PrefRouter.HeadStep request depth before after)
    {physical : RawTree Nat} {trees : List (RawTree Nat)}
    (inventory : Core (routerState before) (separatorReference reference).toRaw physical trees) :
    ∃ final next rotations,
      Core (routerState after) (separatorReference reference).toRaw final next ∧
      Rotations physical final rotations ∧
      (∃ address work,
        routerState after = toggle (routerState before) address ∧
        Switch (routerState before) (separatorReference reference).toRaw address physical final rotations work) ∧
      rotations+2*forestPotential next ≤ 2*forestPotential trees+
        24*Nat.log 2 (separatorReference reference).height+3 := by
  obtain ⟨address,spine,left,pivot,right,path,same⟩ := secondary_head_path reference shape step
  obtain ⟨marked,physicalEq,represented⟩ := inventory.realizes.expose
  have unique := (separatorReference reference).toRaw_ordered.imp (fun less => Nat.ne_of_lt less)
  obtain ⟨main,old,foreign,next,rotations,mainRep,nextInventory,actual,execution,ordinary,bound⟩ :=
    preferred_root_repair path unique represented (physicalEq.symm ▸ inventory)
      (preferred_size_le_height _ (separatorReference reference))
      (preferred_size_le_height _ (separatorReference reference))
  refine ⟨main.erase,next,rotations,?_,?_,?_,bound⟩
  · rw [same]
    exact nextInventory
  · rw [← physicalEq]
    exact actual
  · refine ⟨address,rotations+2+2*spine.lower.count+2*spine.upper.count,same,?_⟩
    rw [← physicalEq]
    exact ordinary

/-- Every repair is the existing ordinary pivot/guard splay algorithm;
the witness is retained in the final execution relation. -/
inductive SecondaryExecution {a b : Nat} (reference : DepthTree a b) (request : Nat) :
    PrefRouter Nat → PrefRouter Nat → RawTree Nat → RawTree Nat → Nat → Prop
  | done (before : PrefRouter Nat) (physical : RawTree Nat) :
      SecondaryExecution reference request before before physical physical 0
  | next {before middle after : PrefRouter Nat} {physical next final : RawTree Nat}
      {depth rotations work last : Nat} {address : ChaCha.Primary.Key}
      (step : PrefRouter.HeadStep request depth before middle)
      (state : routerState middle = toggle (routerState before) address)
      (ordinary : Switch (routerState before) (separatorReference reference).toRaw
        address physical next rotations work)
      (rest : SecondaryExecution reference request middle after next final last) :
      SecondaryExecution reference request before after physical final (rotations+last)

theorem secondary_head_trace {a b : Nat} (reference : DepthTree a b)
    {request : Nat} {before after : PrefRouter Nat} {depths : List Nat}
    (shape : before.erase = LocalReferences.depthReference reference)
    (steps : PrefRouter.HeadTrace request before depths after)
    {physical : RawTree Nat} {trees : List (RawTree Nat)}
    (inventory : Core (routerState before) (separatorReference reference).toRaw physical trees) :
    ∃ final next rotations,
      Core (routerState after) (separatorReference reference).toRaw final next ∧
      Rotations physical final rotations ∧
      SecondaryExecution reference request before after physical final rotations ∧
      rotations+2*forestPotential next ≤ 2*forestPotential trees+
        (24*Nat.log 2 (separatorReference reference).height+3)*depths.length := by
  induction steps generalizing physical trees with
  | nil tree => exact ⟨physical,trees,0,inventory,.refl _,.done _ _,by simp⟩
  | cons step rest ih =>
      obtain ⟨middle,middleTrees,first,middleInventory,firstRun,⟨address,work,same,ordinary⟩,firstBound⟩ :=
        secondary_head_repair reference shape step inventory
      obtain ⟨final,next,last,lastInventory,lastRun,lastOrdinary,lastBound⟩ :=
        ih ((head_erase step).symm.trans shape) middleInventory
      refine ⟨final,next,first+last,lastInventory,firstRun.append lastRun,
        .next step same ordinary lastOrdinary,?_⟩
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega

/-- Actual secondary preference update, paid by exactly the existing
secondary flip counter. The same arbitrary-shape state survives the access. -/
theorem secondary_access {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (request : Nat)
    {physical : RawTree Nat} {trees : List (RawTree Nat)}
    (inventory : Core (routerState (Secondary.decodeDepth reference preference))
      (separatorReference reference).toRaw physical trees) :
    ∃ final next rotations,
      Core (routerState (Secondary.decodeDepth reference (Secondary.intervalUpdate request preference)))
        (separatorReference reference).toRaw final next ∧
      Rotations physical final rotations ∧
      SecondaryExecution reference request (Secondary.decodeDepth reference preference)
        (Secondary.decodeDepth reference (Secondary.intervalUpdate request preference)) physical final rotations ∧
      rotations+2*forestPotential next ≤ 2*forestPotential trees+
        (24*Nat.log 2 (separatorReference reference).height+3)*
          (Secondary.decodeDepth reference preference).accessFlips request := by
  have shape : (Secondary.decodeDepth reference preference).erase =
      LocalReferences.depthReference reference := by
    clear inventory
    induction reference <;> simp_all [Secondary.decodeDepth,PrefRouter.erase,LocalReferences.depthReference]
  have result := secondary_head_trace reference shape
    (PrefRouter.access_headTrace request (Secondary.decodeDepth reference preference)) inventory
  simpa only [Secondary.decodeDepth_access,PrefRouter.exitDepths_length] using result

end ChaCha.Paper20261030.SplayAuxiliary
