import ChaCha.Paper20261030.SplayAuxiliaryGlobalComponents
import ChaCha.Paper20261030.SplayAuxiliaryLeaves
import ChaCha.Paper20261030.PrimaryExitComponents

/-!
# The original-key physical tree from ordinary-splay component states

The component table is indexed by original endpoint keys. Its actual
closed secondary sources determine both routing wings and complete
virtual headers. The global expansion contains exactly the original
ordered leaf word and at most five bounded datums at each vertex.
These conclusions apply to the actual maintained invariant, without
assuming a separate family of valid physical inputs.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary.Physical

open ColoredStorage SecondaryDecomposition
open SplayAuxiliary.Decomposition
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical Secondary

variable {α : Type*} [DecidableEq α]

def closed (component : Global.Component) : Source Nat Nat := component.auxiliary.closed

def active_input {b : Nat} (t : PrefRouter α) (reference : DepthTree 0 b)
    (p : DepthSplit → Bool) (c : Global.Component)
    (represented : Represents cutKey followsRight (source reference p) c.auxiliary)
    (pathLength : (exits t).length = b) : Input t Nat where
  start := 0
  source := closed c
  leaves := Or.inl (by simpa only [closed,pathLength,Nat.sub_zero] using represented_depth_leaves reference p represented)

def dormant_input {b start : Nat} (t : PrefRouter α) (reference : DepthTree 0 b)
    (positive : 0 < start) (valid : start ≤ b) (p : DepthSplit → Bool)
    (c : Global.Component)
    (represented : Represents cutKey followsRight
      (suffixSource reference p (start-1) ⟨Nat.zero_le _,by omega⟩) c.auxiliary)
    (pathLength : (exits t).length = b-start) : Input t Nat where
  start := start
  source := closed c
  leaves := Or.inr ⟨positive,by
    change c.auxiliary.closed.shape.leaves = _
    rw [represented_suffix_leaves reference p (start-1) _ represented,
      filter_suffix_range 0 b (start-1) ⟨Nat.zero_le _,by omega⟩,pathLength]
    have length : b+1-(start-1) = (b-start+1)+1 := by omega
    rw [length,List.range'_succ,show start-1+1 = start by omega]⟩

theorem table_input {height start : Nat} (reference : DepthTree 0 height)
    {whole subtree : PrefRouter α} (perfect : whole.Perfect height)
    (distinct : whole.leaves.Nodup) (memory : MemoryKey → Bool) (components : Global.Table α)
    (valid : Global.Table.Valid reference whole perfect memory components)
    (rooted : ComponentRoot whole start subtree) :
    ValidInput (whole.componentStart subtree.terminal) subtree (closed (components subtree.terminal)) := by
  have endpoint := rooted.endpoint_start distinct
  have member := rooted.leaves_subset subtree.terminal subtree.terminal_mem
  have represented := (valid subtree.terminal member).1
  obtain ⟨bound,childPerfect⟩ := rooted.perfect perfect
  have pathLength := perfect_exits_length childPerfect
  rw [endpoint]
  by_cases active : subtree.terminal = whole.terminal
  · have startZero : start = 0 := by rw [active,PrefRouter.componentStart_terminal] at endpoint; omega
    cases startZero
    simp only [componentSource,if_pos active] at represented
    exact (active_input subtree reference (ownerBits whole subtree.terminal memory)
      (components subtree.terminal) represented pathLength).leaves
  · have positive : 0 < start := by
      have nonzero := (PrefRouter.componentStart_zero_iff member).not.mpr active
      omega
    simp only [componentSource,if_neg active,endpoint] at represented
    exact (dormant_input subtree reference positive bound
      (intervalUpdate (start-1) (ownerBits whole subtree.terminal memory))
      (components subtree.terminal) represented pathLength).leaves

def storedPlan (starts : α → Nat) (components : Global.Table α) (subtree : PrefRouter α) :
    Plan α (Datum Nat) :=
  let routing := PackedPrimary.plan (starts subtree.terminal) subtree (closed (components subtree.terminal))
  ⟨liftWing routing.left,liftWing routing.right⟩

def storedHeader (starts : α → Nat) (components : Global.Table α) (subtree : PrefRouter α) :
    List (Datum Nat) :=
  canonicalHeaders (starts subtree.terminal) subtree (closed (components subtree.terminal))

def storedTree (starts : α → Nat) (components : Global.Table α) (subtree : PrefRouter α) :
    Source α (List (Option (Datum Nat))) :=
  expand (storedPlan starts components) (storedHeader starts components) subtree

theorem storedPlan_bounded (starts : α → Nat) (components : Global.Table α) (subtree : PrefRouter α) :
    RoutingBounded 3 (storedPlan starts components subtree).left ∧
      RoutingBounded 3 (storedPlan starts components subtree).right := by
  have bounds := plan_bounded (starts subtree.terminal) subtree (closed (components subtree.terminal))
  exact ⟨liftWing_bounded bounds.1,liftWing_bounded bounds.2⟩

theorem storedTree_bounded (starts : α → Nat) (components : Global.Table α) (subtree : PrefRouter α) :
    (storedTree starts components subtree).Bounded 5 :=
  expand_bounded _ _ 3 1 (storedPlan_bounded starts components)
    (fun t => canonicalHeaders_size _ t _) subtree

theorem storedTree_root_bound (starts : α → Nat) (components : Global.Table α) (subtree : PrefRouter α) :
    (storedTree starts components subtree).rootRecord.length ≤ 1 :=
  (expand_root_bound _ _ subtree).trans (canonicalHeaders_size _ subtree _)

theorem storedPlan_words {starts : α → Nat} {components : Global.Table α} {subtree : PrefRouter α}
    (valid : ValidInput (starts subtree.terminal) subtree (closed (components subtree.terminal))) :
    routingWord (storedPlan starts components subtree).left = (exits subtree).filter (·.leftOfEndpoint) ∧
      routingWord (storedPlan starts components subtree).right =
        ((exits subtree).filter (fun e => !e.leftOfEndpoint)).reverse :=
  (Input.mk (starts subtree.terminal) (closed (components subtree.terminal)) valid).completePlan_words

theorem storedTree_leaves {height start : Nat} (reference : DepthTree 0 height)
    {whole subtree : PrefRouter α} (perfect : whole.Perfect height)
    (distinct : whole.leaves.Nodup) (memory : MemoryKey → Bool) (components : Global.Table α)
    (valid : Global.Table.Valid reference whole perfect memory components)
    (rooted : ComponentRoot whole start subtree) :
    (storedTree whole.componentStart components subtree).shape.leaves = subtree.leaves := by
  have inputValid := table_input reference perfect distinct memory components valid rooted
  obtain ⟨leftWord,rightWord⟩ := storedPlan_words inputValid
  let payload := fun e => if member : e ∈ exits subtree then
    storedTree whole.componentStart components e.subtree else .leaf subtree.terminal []
  have words : ∀ e ∈ exits subtree, (payload e).shape.leaves = e.subtree.leaves := by
    intro e he
    dsimp only [payload]
    rw [dif_pos he]
    obtain ⟨depth,present⟩ := List.mem_iff_getElem?.mp he
    have child := rooted.child (show portAt 0 (exits subtree) depth = some e by simpa [portAt] using present)
    exact storedTree_leaves reference perfect distinct memory components valid child
  change (expand _ _ subtree).shape.leaves = _
  rw [PrimaryPhysical.expand,PrimaryPhysical.component_leaves,graftWing_leaves,graftWing_leaves,leftWord,rightWord]
  have hl := List.flatMap_congr (l := (exits subtree).filter (·.leftOfEndpoint))
    (f := fun e => (payload e).shape.leaves) (g := fun e => e.subtree.leaves)
    (fun e he => words e (List.mem_filter.mp he).1)
  have hr := List.flatMap_congr (l := ((exits subtree).filter (fun e => !e.leftOfEndpoint)).reverse)
    (f := fun e => (payload e).shape.leaves) (g := fun e => e.subtree.leaves)
    (fun e he => words e (List.mem_filter.mp (List.mem_reverse.mp he)).1)
  dsimp only [payload,storedTree] at hl hr
  rw [hl,hr]
  exact (leaf_partition subtree).symm
termination_by subtree.leaves.length
decreasing_by exact exit_smaller (by assumption)

def physicalState (primary : PrefRouter α) (components : Global.Table α) :
    Source α (List (Option (Datum Nat))) := storedTree primary.componentStart components primary

theorem physicalState_bounded (primary : PrefRouter α) (components : Global.Table α) :
    (physicalState primary components).Bounded 5 := storedTree_bounded _ _ _

theorem physical_leaves {height : Nat} (reference : DepthTree 0 height)
    {primary : PrefRouter α} (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup)
    (memory : MemoryKey → Bool) (components : Global.Table α)
    (valid : Global.Table.Valid reference primary perfect memory components) :
    (physicalState primary components).shape.leaves = primary.leaves :=
  storedTree_leaves reference perfect distinct memory components valid .root

end ChaCha.Paper20261030.SplayAuxiliary.Physical
