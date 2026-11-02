import ChaCha.Paper20261030.LocalSecondaryRepair
import ChaCha.Paper20261030.ObservedSecondaryAccess

/-! The actual secondary preference-update loop. After every successful
repair the program starts another local departure query. A no-departure
answer halts. The execution and total cost follow the existing abstract
head trace, without storing that trace or a preference table at runtime. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.AccessController

open PreferredProjection ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourceLocalProgram

abbrev State := RepairController.State

def initial : State := .selecting (.first .start)

def advance : State → State
  | .done true => initial
  | state => state

def program (request : Nat) : Program State Cached :=
  fun state => (RepairController.program request state).mapState advance

def bound {a b : Nat} (reference : DepthTree a b) :=
  130857*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+973

theorem code (request : Nat) (state : State) (active : RepairController.program request state ≠ .halt) :
    program request (advance state) = (RepairController.program request state).mapState advance := by
  cases state with
  | selecting | repairing => rfl
  | done changed => exact False.elim (active rfl)

theorem head_trace {a b : Nat} (reference : DepthTree a b)
    {request : Nat} {before after : PrefRouter Nat} {depths : List Nat}
    (steps : PrefRouter.HeadTrace request before depths after)
    (preferences : DepthSplit → Bool) (decoded : Secondary.decodeDepth reference preferences = before)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component) (outside) :
    ∃ (last : DepthSplit → Bool) (out : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Secondary.decodeDepth reference last = after ∧ Represents followsRight (source reference last) out ∧
      ∃ reads cost, Steps (program request) initial ⟨closed component,outside⟩ initial ⟨closed out,outside⟩ reads cost ∧
        cost ≤ depths.length*bound reference := by
  induction steps generalizing preferences component with
  | nil tree => exact ⟨preferences,component,decoded,represented,[],0,.nil _ _,by simp⟩
  | cons step rest ih =>
    rw [← decoded] at step
    obtain ⟨pivot,middle,middleDecoded,middleRep,firstReads,firstCost,firstRun,firstBound⟩ :=
      RepairController.head_step reference preferences step component represented outside
    obtain ⟨last,out,lastDecoded,outRep,lastReads,lastCost,lastRun,lastBound⟩ :=
      ih (Function.update preferences pivot.split (!preferences pivot.split)) middleDecoded middle middleRep
    have first := firstRun.map_prefix advance (code request)
    have full := first.append lastRun
    refine ⟨last,out,lastDecoded,outRep,_,_,full,?_⟩
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    unfold bound at *
    omega

theorem access {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (valid : a ≤ request ∧ request ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component) (outside) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Secondary.intervalUpdate request preferences)) out ∧
      ∃ reads cost, Run (program request) initial ⟨closed component,outside⟩ (.done false)
        ⟨closed out,outside⟩ reads cost ∧
        cost ≤ ((Secondary.decodeDepth reference preferences).accessFlips request+1)*bound reference := by
  obtain ⟨last,out,decoded,outRep,firstReads,firstCost,firstRun,firstBound⟩ := head_trace reference
    (PrefRouter.access_headTrace request (Secondary.decodeDepth reference preferences)) preferences rfl component represented outside
  have same := source_of_decode_eq reference last (Secondary.intervalUpdate request preferences)
    (decoded.trans (Secondary.decodeDepth_access reference preferences request).symm)
  rw [same] at outRep
  rw [PrefRouter.exitDepths_length] at firstBound
  have endpoint : (Secondary.decodeDepth reference (Secondary.intervalUpdate request preferences)).terminal = request := by
    rw [Secondary.decodeDepth_access]
    exact PrefRouter.terminal_access _ _ ((Secondary.decodeDepth_mem reference preferences request).mpr valid)
  obtain ⟨lastReads,lastCost,lastRun,lastBound⟩ := RepairController.terminal reference
    (Secondary.intervalUpdate request preferences) out outRep outside
  rw [endpoint] at lastRun
  have stopped := lastRun.map_prefix advance (code request)
  have full := firstRun.append stopped
  have size := represented_size reference (Secondary.intervalUpdate request preferences) out outRep
  have rank := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  refine ⟨out,outRep,_,_,full.run rfl,?_⟩
  rw [Nat.add_mul,Nat.one_mul]
  unfold bound at *
  omega

end ChaCha.Paper20261030.SecondaryDecomposition.AccessController
