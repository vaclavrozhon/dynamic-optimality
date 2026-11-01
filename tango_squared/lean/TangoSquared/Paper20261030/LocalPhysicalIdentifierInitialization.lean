import TangoSquared.Paper20261030.LocalPhysicalBoundaryRepair
import TangoSquared.Paper20261030.MultiSourceStationaryFingers

/-!
# Allocating physical identifiers by an actual depth-first traversal

The input tree may contain arbitrary old metadata. The program reads its
leaf bit, preserves its application payload, and assigns successive natural
identifiers starting at a supplied counter. The counter is never used as
a pointer. The only navigation is to a child or to the parent.

One temporary bit at each vertex records whether the left subtree has
finished. Parent and child identifiers are written during the same tour.
The program receives neither the tree shape nor a traversal stack. All
temporary bits are true at completion. This initializes the physical
identifier layer; constructing the logical Tango decomposition remains
a separate initialization step.
-/

namespace TangoSquared.Paper20261030.PhysicalIdentifierInitialization

open ColoredStorage SourcePointer SourceLocalProgram Structural

variable {α ρ : Type*}

abbrev Cell (ρ : Type*) := ((Nat × ρ) × Fields Nat Unit) × Bool

def child (id : Nat) : Child Nat Unit := ⟨id,{()}⟩

def cell (payload : ρ) (id : Nat) (parent : Option Nat) (children : Option (Nat × Nat)) (done : Bool) : Cell ρ :=
  (((id,payload),⟨parent,{()},children.map (fun ids => (child ids.1,child ids.2))⟩),done)

inductive Continuation where
  | finish (counter : Nat) (parent : Option Nat)
  | descend (right : Bool) (parent counter : Nat)

inductive State (ρ : Type*) where
  | enter (counter : Nat) (parent : Option Nat)
  | returned (counter : Nat)
  | writing (fresh : Cell ρ) (next : Continuation)
  | continue (next : Continuation)

def entering (counter : Nat) (parent : Option Nat) (record : Cell ρ) (leaf : Bool) : State ρ :=
  if leaf then .writing (cell record.1.1.2 counter parent none true) (.finish (counter+1) parent)
  else .writing (cell record.1.1.2 counter parent (some (counter+1,0)) false)
    (.descend false counter (counter+1))

def returning (counter : Nat) (record : Cell ρ) : State ρ :=
  if record.2 then .continue (.finish counter record.1.2.parent)
  else .writing (cell record.1.1.2 record.1.1.1 record.1.2.parent
    (some (record.1.1.1+1,counter)) true) (.descend true record.1.1.1 counter)

def program : Program (State ρ) (Cell ρ)
  | .enter counter parent => .read (entering counter parent)
  | .returned counter => .read (fun record _ => returning counter record)
  | .writing fresh next => .write fresh (.continue next)
  | .continue (.finish _ none) => .halt
  | .continue (.finish counter (some _)) => .nav .up (.returned counter)
  | .continue (.descend right parent counter) => .nav (if right then .right else .left) (.enter counter (some parent))

def count {τ : Type*} : Source α τ → Nat
  | .leaf _ _ => 1
  | .fork _ left right => 1+count left+count right

def initialized (start : Nat) (parent : Option Nat) : Source α (Cell ρ) → Source α (Cell ρ)
  | .leaf key record => .leaf key (cell record.1.1.2 start parent none true)
  | .fork record left right =>
    .fork (cell record.1.1.2 start parent (some (start+1,start+1+count left)) true)
      (initialized (start+1) (some start) left)
      (initialized (start+1+count left) (some start) right)

def cost {τ : Type*} : Source α τ → Nat
  | .leaf _ _ => 2
  | .fork _ left right => 9+cost left+cost right

theorem allocate (source : Source α (Cell ρ)) (start : Nat) (parent : Option Nat) (outside) :
    ∃ reads, Steps program (.enter start parent) ⟨source,outside⟩
      (.continue (.finish (start+count source) parent)) ⟨initialized start parent source,outside⟩ reads (cost source) := by
  induction source generalizing start parent outside with
  | leaf key record =>
    have first : Step program (.enter start parent) ⟨.leaf key record,outside⟩
        (.writing (cell record.1.1.2 start parent none true) (.finish (start+1) parent))
        ⟨.leaf key record,outside⟩ (some record) := by
      simpa only [entering,isLeaf,if_true,Source.rootRecord] using
        (Step.read (program := program) (state := .enter start parent)
          (next := entering start parent) (cursor := ⟨.leaf key record,outside⟩) rfl)
    have last : Step program (.writing (cell record.1.1.2 start parent none true) (.finish (start+1) parent))
        ⟨.leaf key record,outside⟩ (.continue (.finish (start+1) parent))
        ⟨.leaf key (cell record.1.1.2 start parent none true),outside⟩ none := .write rfl
    exact ⟨[record],.next first last.prefix⟩
  | fork record left right ihl ihr =>
    let firstRecord := cell record.1.1.2 start parent (some (start+1,0)) false
    let lastRecord := cell record.1.1.2 start parent (some (start+1,start+1+count left)) true
    let newLeft := initialized (start+1) (some start) left
    let newRight := initialized (start+1+count left) (some start) right
    have readRoot : Step program (.enter start parent) ⟨.fork record left right,outside⟩
        (.writing firstRecord (.descend false start (start+1))) ⟨.fork record left right,outside⟩ (some record) := by
      simpa only [entering,isLeaf,Bool.false_eq_true,if_false,firstRecord,Source.rootRecord] using
        (Step.read (program := program) (state := .enter start parent)
          (next := entering start parent) (cursor := ⟨.fork record left right,outside⟩) rfl)
    have writeRoot : Step program (.writing firstRecord (.descend false start (start+1)))
        ⟨.fork record left right,outside⟩ (.continue (.descend false start (start+1)))
        ⟨.fork firstRecord left right,outside⟩ none := .write rfl
    have downLeft : Step program (.continue (.descend false start (start+1)))
        ⟨.fork firstRecord left right,outside⟩ (.enter (start+1) (some start))
        ⟨left,.left firstRecord right :: outside⟩ none := .nav rfl rfl
    obtain ⟨leftReads,leftRun⟩ := ihl (start+1) (some start) (.left firstRecord right :: outside)
    have upLeft : Step program (.continue (.finish (start+1+count left) (some start)))
        ⟨newLeft,.left firstRecord right :: outside⟩ (.returned (start+1+count left))
        ⟨.fork firstRecord newLeft right,outside⟩ none := .nav rfl rfl
    have readLeft : Step program (.returned (start+1+count left)) ⟨.fork firstRecord newLeft right,outside⟩
        (.writing lastRecord (.descend true start (start+1+count left)))
        ⟨.fork firstRecord newLeft right,outside⟩ (some firstRecord) := by
      simpa only [returning,firstRecord,cell,Bool.false_eq_true,if_false,lastRecord,Source.rootRecord] using
        (Step.read (program := program) (next := fun record _ => returning (start+1+count left) record)
          (state := .returned (start+1+count left)) (cursor := ⟨.fork firstRecord newLeft right,outside⟩) rfl)
    have writeRight : Step program (.writing lastRecord (.descend true start (start+1+count left)))
        ⟨.fork firstRecord newLeft right,outside⟩ (.continue (.descend true start (start+1+count left)))
        ⟨.fork lastRecord newLeft right,outside⟩ none := .write rfl
    have downRight : Step program (.continue (.descend true start (start+1+count left)))
        ⟨.fork lastRecord newLeft right,outside⟩ (.enter (start+1+count left) (some start))
        ⟨right,.right newLeft lastRecord :: outside⟩ none := .nav rfl rfl
    obtain ⟨rightReads,rightRun⟩ := ihr (start+1+count left) (some start) (.right newLeft lastRecord :: outside)
    have upRight : Step program (.continue (.finish (start+1+count left+count right) (some start)))
        ⟨newRight,.right newLeft lastRecord :: outside⟩ (.returned (start+1+count left+count right))
        ⟨.fork lastRecord newLeft newRight,outside⟩ none := .nav rfl rfl
    have readRight : Step program (.returned (start+1+count left+count right)) ⟨.fork lastRecord newLeft newRight,outside⟩
        (.continue (.finish (start+1+count left+count right) parent))
        ⟨.fork lastRecord newLeft newRight,outside⟩ (some lastRecord) := by
      simpa only [returning,lastRecord,cell,if_true,Source.rootRecord] using
        (Step.read (program := program) (next := fun record _ => returning (start+1+count left+count right) record)
          (state := .returned (start+1+count left+count right)) (cursor := ⟨.fork lastRecord newLeft newRight,outside⟩) rfl)
    have actual := readRoot.prefix.append (writeRoot.prefix.append (downLeft.prefix.append
      (leftRun.append (upLeft.prefix.append (readLeft.prefix.append (writeRight.prefix.append
        (downRight.prefix.append (rightRun.append (upRight.prefix.append readRight.prefix)))))))))
    have countEq : start+1+count left+count right = start+count (.fork record left right) := by
      simp only [count]; omega
    have costEq : 1+(1+(1+(cost left+(1+(1+(1+(1+(cost right+(1+1))))))))) = cost (.fork record left right) := by
      simp only [cost]; omega
    rw [countEq,costEq] at actual
    refine ⟨[record]++leftReads++[firstRecord]++rightReads++[lastRecord],?_⟩
    simpa only [initialized,lastRecord,newLeft,newRight,Option.toList_some,Option.toList_none,
      List.nil_append,List.append_nil,List.append_assoc] using actual

theorem run (source : Source α (Cell ρ)) (start : Nat) :
    ∃ reads, Run program (.enter start none) ⟨source,[]⟩
      (.continue (.finish (start+count source) none)) ⟨initialized start none source,[]⟩ reads (cost source) := by
  obtain ⟨reads,actual⟩ := allocate source start none []
  exact ⟨reads,actual.run rfl⟩

theorem cost_leaves {τ : Type*} (source : Source α τ) : cost source+9 = 11*source.shape.leaves.length := by
  induction source with
  | leaf => rfl
  | fork record left right ihl ihr =>
    simp only [cost,Source.shape,RouterProjection.Router.leaves,List.length_append]
    omega

def assigned (start : Nat) : Source α (Cell ρ) → Source α (Nat × ρ)
  | .leaf key record => .leaf key (start,record.1.1.2)
  | .fork record left right => .fork (start,record.1.1.2)
      (assigned (start+1) left) (assigned (start+1+count left) right)

theorem assigned_root (start : Nat) (source : Source α (Cell ρ)) :
    (assigned start source).rootRecord.1 = start := by cases source <;> rfl

/-- All stored physical parent and child fields have their canonical
meaning, not merely the right shape or an unchanged inventory. -/
theorem metadata (start : Nat) (parent : Option Nat) (source : Source α (Cell ρ)) :
    initialized start parent source =
      (annotate Prod.fst (fun _ => (() : Unit)) parent (assigned start source)).mapRecords (fun record => (record,true)) := by
  induction source generalizing start parent with
  | leaf => rfl
  | fork record left right ihl ihr =>
    simp only [initialized,assigned,annotate,Source.mapRecords,fields,descriptor,
      Source.support,PhysicalBoundaryRepair.unit_support,Finset.union_self,assigned_root,
      ihl,ihr,cell,child,Option.map_some]

theorem payload_unchanged (start : Nat) (parent : Option Nat) (source : Source α (Cell ρ)) :
    (initialized start parent source).mapRecords (fun record => record.1.1.2) =
      source.mapRecords (fun record => record.1.1.2) := by
  induction source generalizing start parent <;> simp_all only [initialized,Source.mapRecords,cell]

theorem identifier_inventory (start : Nat) (parent : Option Nat) (source : Source α (Cell ρ)) :
    (initialized start parent source).inventory (fun record => record.1.1.1) = (List.range' start (count source) : Multiset Nat) := by
  induction source generalizing start parent with
  | leaf => simp only [initialized,Source.inventory_leaf,cell,count,List.range'_succ,List.range'_zero,Multiset.coe_singleton]
  | fork record left right ihl ihr =>
    simp only [initialized,Source.inventory_fork,cell,ihl,ihr,count]
    have split : List.range' start (1+count left+count right) =
        start :: (List.range' (start+1) (count left) ++ List.range' (start+1+count left) (count right)) := by
      have sizeEq : 1+count left+count right = (count left+count right)+1 := by omega
      rw [sizeEq,List.range'_succ,← List.range'_append_1]
    rw [split]
    change {start} + (List.range' (start+1) (count left) : Multiset Nat) +
        (List.range' (start+1+count left) (count right) : Multiset Nat) =
      ({start} + ((List.range' (start+1) (count left) ++ List.range' (start+1+count left) (count right) : List Nat) : Multiset Nat))
    exact add_assoc _ _ _

theorem unique (start : Nat) (parent : Option Nat) (source : Source α (Cell ρ)) :
    ((initialized start parent source).inventory (fun record => record.1.1.1)).Nodup := by
  rw [identifier_inventory,Multiset.coe_nodup]
  exact List.nodup_range'

theorem identifier_bounds (start : Nat) (parent : Option Nat) (source : Source α (Cell ρ))
    (id : Nat) (member : id ∈ (initialized start parent source).inventory (fun record => record.1.1.1)) :
    start ≤ id ∧ id < start+count source := by
  rw [identifier_inventory,Multiset.mem_coe,List.mem_range'_1] at member
  exact member

def workingRecords : State ρ → Nat
  | .writing _ _ => 1
  | _ => 0

theorem working_records (state : State ρ) : workingRecords state ≤ 1 := by
  cases state <;> simp only [workingRecords] <;> omega

theorem edgeOnly : MultiSourceSingleCursor.EdgeOnly (program (ρ := ρ)) := by
  intro state action next instruction
  cases state with
  | enter | returned | writing => simp only [program,reduceCtorEq] at instruction
  | «continue» next => cases next with
    | finish counter parent =>
      cases parent <;> simp only [program,reduceCtorEq,Instruction.nav.injEq] at instruction
      rcases instruction with ⟨rfl,_⟩
      trivial
    | descend right parent counter =>
      cases right <;> simp only [program,Bool.false_eq_true,if_false,if_true,Instruction.nav.injEq] at instruction
      all_goals rcases instruction with ⟨rfl,_⟩; trivial

/-- Execute the allocation on the whole shared physical tree. Every
finger retains its address, and the identifier inventory is globally
distinct, including the vertices used only as component connectors. -/
theorem execute {F : Type*} [DecidableEq F] (finger : F) (start : Nat)
    (config : MultiSourceProgram.Configuration F α (Cell ρ))
    (positioned : config.fingers finger = some []) (valid : MultiSourceProgram.WellFormed config) :
    ∃ target reads,
      MultiSourceProgram.Run (MultiSourceSingleCursor.program program finger)
        (some (.enter start none)) config (some (.continue (.finish (start+count config.tree) none))) target reads (cost config.tree) ∧
      target.tree = initialized start none config.tree ∧ target.fingers = config.fingers ∧
      MultiSourceProgram.WellFormed target ∧
      (target.tree.inventory (fun record => record.1.1.1)).Nodup := by
  obtain ⟨reads,actual⟩ := run config.tree start
  obtain ⟨target,compiled,targetRep,others⟩ :=
    MultiSourceSingleCursor.compile_edge_run program edgeOnly finger actual config ⟨rfl,positioned⟩
  refine ⟨target,_,compiled,targetRep.1,?_,compiled.wellFormed valid,?_⟩
  · funext other
    by_cases same : other = finger
    · subst other
      exact targetRep.2.trans positioned.symm
    · exact others other same
  · rw [targetRep.1]
    exact unique start none config.tree

end TangoSquared.Paper20261030.PhysicalIdentifierInitialization
