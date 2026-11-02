import ChaCha.Paper20261030.SplayAuxiliaryReferencePorts

/-!
# Ordinary-splay secondary access on arbitrary full source references

Dormant primary paths use suffix references with suppressed unary vertices.
The access proof depends only on their unchanged separator keys, leaf
shape, and reference height; no interval-tree constructor is required.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open DynamicOptimality.SearchRotation
open ColoredStorage PreferredProjection
open MultiSplay EndpointEncoding ClassicalSwitch Global.Preferred

variable {α ρ κ : Type*} [DecidableEq α]

theorem preferred_source_height (key : ρ → κ) (reference : Source α ρ) (state : State) :
    (preferred state (referenceCuts key reference)).size ≤ reference.shape.height := by
  induction reference generalizing state with
  | leaf => exact Nat.le_refl _
  | fork record l r ihl ihr =>
      have left := ihl (below state false)
      have right := ihr (below state true)
      cases direction : state [] <;>
        simp only [referenceCuts,preferred,direction,Bool.false_eq_true,if_false,if_true,
          MTR.Tree.size,Source.shape,RouterProjection.Router.height] <;> omega

private theorem toggle_source_root (bit : Bool) (left right : PrefRouter α) :
    routerState (.fork (!bit) left right) = toggle (routerState (.fork bit left right)) [] := by
  funext owner
  cases owner with
  | nil => simp [routerState,toggle]
  | cons side rest => cases side <;> simp [routerState,toggle]

private theorem toggle_source_left (bit : Bool) (left after right : PrefRouter α)
    (address : ChaCha.Primary.Key) (same : routerState after = toggle (routerState left) address) :
    routerState (.fork bit after right) = toggle (routerState (.fork bit left right)) (false::address) := by
  funext owner
  cases owner with
  | nil => simp [routerState,toggle]
  | cons side rest =>
      cases side <;> simp [routerState,toggle,List.cons.injEq]
      exact congrFun same rest

private theorem toggle_source_right (bit : Bool) (left right after : PrefRouter α)
    (address : ChaCha.Primary.Key) (same : routerState after = toggle (routerState right) address) :
    routerState (.fork bit left after) = toggle (routerState (.fork bit left right)) (true::address) := by
  funext owner
  cases owner with
  | nil => simp [routerState,toggle]
  | cons side rest =>
      cases side <;> simp [routerState,toggle,List.cons.injEq]
      exact congrFun same rest

theorem source_head_path (key : ρ → κ) (reference : Source α ρ)
    {request : α} {depth : Nat} {before after : PrefRouter α}
    (shape : before.erase = reference.shape)
    (step : PrefRouter.HeadStep request depth before after) :
    ∃ address spine left pivot right,
      Path (routerState before) (referenceCuts key reference) address spine
        (.node left pivot right) ∧
      routerState after = toggle (routerState before) address := by
  induction reference generalizing before after depth with
  | leaf label record =>
      cases before with
      | leaf value => cases step
      | fork bit left right => simp [PrefRouter.erase,Source.shape] at shape
  | fork record left right ihl ihr =>
      cases before with
      | leaf value => simp [PrefRouter.erase,Source.shape] at shape
      | fork bit l r =>
          have shapes := RouterProjection.Router.fork.inj shape
          cases step with
          | leftRoot _ _ member =>
              exact ⟨[],[],_,key record,_,.here _ _,toggle_source_root true l r⟩
          | rightRoot _ _ absent member =>
              exact ⟨[],[],_,key record,_,.here _ _,toggle_source_root false l r⟩
          | @leftDown depth l l' r step =>
              obtain ⟨address,spine,x,pivot,y,path,same⟩ := ihl shapes.1 step
              refine ⟨false::address,spine++[(false,key record)],x,pivot,y,?_,?_⟩
              · exact .left rfl path
              · exact toggle_source_left false l l' r address same
          | @rightDown depth r r' l absent step =>
              obtain ⟨address,spine,x,pivot,y,path,same⟩ := ihr shapes.2 step
              refine ⟨true::address,spine++[(true,key record)],x,pivot,y,?_,?_⟩
              · exact .right rfl path
              · exact toggle_source_right true l r r' address same

/-- Complete algorithmic provenance for the generic source-reference case. -/
inductive SourceSecondaryExecution (key : ρ → κ) (reference : Source α ρ) (request : α) :
    PrefRouter α → PrefRouter α → RawTree κ → RawTree κ → Nat → Prop
  | done (before : PrefRouter α) (physical : RawTree κ) :
      SourceSecondaryExecution key reference request before before physical physical 0
  | next {before middle after : PrefRouter α} {physical next final : RawTree κ}
      {depth rotations work last : Nat} {address : ChaCha.Primary.Key}
      (step : PrefRouter.HeadStep request depth before middle)
      (state : routerState middle = toggle (routerState before) address)
      (ordinary : Switch (routerState before) (referenceCuts key reference)
        address physical next rotations work)
      (rest : SourceSecondaryExecution key reference request middle after next final last) :
      SourceSecondaryExecution key reference request before after physical final (rotations+last)

theorem source_head_repair (key : ρ → κ) (reference : Source α ρ)
    (unique : (referenceCuts key reference).inorder.Nodup)
    {request : α} {depth : Nat} {before after : PrefRouter α}
    (shape : before.erase = reference.shape)
    (step : PrefRouter.HeadStep request depth before after)
    {physical : RawTree κ} {trees : List (RawTree κ)}
    (inventory : Core (routerState before) (referenceCuts key reference) physical trees) :
    ∃ final next rotations,
      Core (routerState after) (referenceCuts key reference) final next ∧
      Rotations physical final rotations ∧
      (∃ address work,
        routerState after = toggle (routerState before) address ∧
        Switch (routerState before) (referenceCuts key reference) address physical final rotations work) ∧
      rotations+2*forestPotential next ≤ 2*forestPotential trees+
        24*Nat.log 2 reference.shape.height+3 := by
  obtain ⟨address,spine,left,pivot,right,path,same⟩ := source_head_path key reference shape step
  obtain ⟨marked,physicalEq,represented⟩ := inventory.realizes.expose
  obtain ⟨main,old,foreign,next,rotations,mainRep,nextInventory,actual,execution,ordinary,bound⟩ :=
    preferred_root_repair path unique represented (physicalEq.symm ▸ inventory)
      (preferred_source_height key reference _) (preferred_source_height key reference _)
  refine ⟨main.erase,next,rotations,?_,?_,?_,bound⟩
  · rw [same]
    exact nextInventory
  · rw [← physicalEq]
    exact actual
  · refine ⟨address,rotations+2+2*spine.lower.count+2*spine.upper.count,same,?_⟩
    rw [← physicalEq]
    exact ordinary

theorem source_head_trace (key : ρ → κ) (reference : Source α ρ)
    (unique : (referenceCuts key reference).inorder.Nodup)
    {request : α} {before after : PrefRouter α} {depths : List Nat}
    (shape : before.erase = reference.shape)
    (steps : PrefRouter.HeadTrace request before depths after)
    {physical : RawTree κ} {trees : List (RawTree κ)}
    (inventory : Core (routerState before) (referenceCuts key reference) physical trees) :
    ∃ final next rotations,
      Core (routerState after) (referenceCuts key reference) final next ∧
      Rotations physical final rotations ∧
      SourceSecondaryExecution key reference request before after physical final rotations ∧
      rotations+2*forestPotential next ≤ 2*forestPotential trees+
        (24*Nat.log 2 reference.shape.height+3)*depths.length := by
  induction steps generalizing physical trees with
  | nil tree => exact ⟨physical,trees,0,inventory,.refl _,.done _ _,by simp⟩
  | cons step rest ih =>
      obtain ⟨middle,middleTrees,first,middleInventory,firstRun,⟨address,work,same,ordinary⟩,firstBound⟩ :=
        source_head_repair key reference unique shape step inventory
      obtain ⟨final,next,last,lastInventory,lastRun,lastOrdinary,lastBound⟩ :=
        ih ((head_erase step).symm.trans shape) middleInventory
      refine ⟨final,next,first+last,lastInventory,firstRun.append lastRun,
        .next step same ordinary lastOrdinary,?_⟩
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega

theorem source_access (key : ρ → κ) (reference : Source α ρ)
    (unique : (referenceCuts key reference).inorder.Nodup)
    (before : PrefRouter α) (shape : before.erase = reference.shape) (request : α)
    {physical : RawTree κ} {trees : List (RawTree κ)}
    (inventory : Core (routerState before) (referenceCuts key reference) physical trees) :
    ∃ final next rotations,
      Core (routerState (before.access request)) (referenceCuts key reference) final next ∧
      Rotations physical final rotations ∧
      SourceSecondaryExecution key reference request before (before.access request) physical final rotations ∧
      rotations+2*forestPotential next ≤ 2*forestPotential trees+
        (24*Nat.log 2 reference.shape.height+3)*before.accessFlips request := by
  simpa only [PrefRouter.exitDepths_length] using
    source_head_trace key reference unique shape (PrefRouter.access_headTrace request before) inventory

end ChaCha.Paper20261030.SplayAuxiliary
