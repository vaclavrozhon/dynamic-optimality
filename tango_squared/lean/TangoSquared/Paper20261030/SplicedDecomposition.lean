import TangoSquared.Paper20261030.SplicedSource
import TangoSquared.Paper20261030.PreparedPathAgreement

/-!
# The exact root-port exchange realizes the persistent-memory splice

Keep the active component's ports strictly before its prepared terminal,
and replace the remaining port word by the incoming dormant component's
whole port word. This combines precisely the old prefix memories with
the incoming suffix memories. The proof constructs the maintained
reference decomposition and retains every attached component whole.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem splicedRepresentative_exists {a b : Nat} (reference : DepthTree a b)
    (p q : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight (suffixSource reference q d valid) incoming) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (splicedSource reference p q d valid) out ∧
      out.portWord = active.portWord.take (terminalIndex followsRight (source reference p)) ++
        incoming.portWord := by
  induction reference generalizing active incoming with
  | leaf a =>
    refine ⟨incoming,incomingRep,?_⟩
    simp only [source,terminalIndex,List.take_zero,List.nil_append]
  | @node a b cut ha hb l r ihl ihr =>
    have sameBit := (SeparatorPath.terminal_root_direction ha hb l r p d preparedP).trans
      (SeparatorPath.terminal_root_direction ha hb l r q d preparedQ).symm
    cases bit : p ⟨a,cut,b⟩
    · have qbit : q ⟨a,cut,b⟩ = false := sameBit.symm.trans bit
      have leftP : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,Bool.false_eq_true,if_false] using preparedP
      have leftQ : (Secondary.decodeDepth l q).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,qbit,Bool.false_eq_true,if_false] using preparedQ
      have bounds := (Secondary.decodeDepth_mem l p d).mp
        (by rw [← leftP]; exact PrefRouter.terminal_mem _)
      obtain ⟨al,ar,hal,har,activeSame⟩ := activeRep.left_view (by exact bit)
      simp only [suffixSource,dif_pos bounds.2] at incomingRep
      obtain ⟨il,ir,hil,hir,incomingSame⟩ := incomingRep.left_view (by exact qbit)
      obtain ⟨ol,hol,ports⟩ := ihl bounds leftP leftQ al il hal hil
      let out := append ol cut ((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false) (closed ir)
      have represented : Represents followsRight (splicedSource (.node cut ha hb l r) p q d valid) out := by
        simp only [splicedSource,dif_pos bounds.2]
        exact .left bit rfl hol hir (.refl _)
      refine ⟨out,represented,?_⟩
      simp only [source,terminalIndex,followsRight,bit,Bool.false_eq_true,if_false]
      rw [activeSame.portWord,incomingSame.portWord]
      simp only [out,append_portWord,ports]
      have bound : terminalIndex followsRight (source l p) ≤ al.portWord.length := by
        rw [portWord_length]
        have := hal.terminalIndex_bound
        omega
      rw [List.take_append_of_le_length bound,List.append_assoc]
    · have qbit : q ⟨a,cut,b⟩ = true := sameBit.symm.trans bit
      have rightP : (Secondary.decodeDepth r p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,bit,if_true] using preparedP
      have rightQ : (Secondary.decodeDepth r q).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,qbit,if_true] using preparedQ
      have bounds := (Secondary.decodeDepth_mem r p d).mp
        (by rw [← rightP]; exact PrefRouter.terminal_mem _)
      have notLeft : ¬ d ≤ cut := by omega
      obtain ⟨al,ar,hal,har,activeSame⟩ := activeRep.right_view (by exact bit)
      simp only [suffixSource,dif_neg notLeft] at incomingRep
      obtain ⟨orep,horep,ports⟩ := ihr bounds rightP rightQ ar incoming har incomingRep
      let out := prepend cut ((⟨a,cut,b⟩,p ⟨a,cut,b⟩),false) (closed al) orep
      have represented : Represents followsRight (splicedSource (.node cut ha hb l r) p q d valid) out := by
        simp only [splicedSource,dif_neg notLeft]
        exact .right bit rfl hal horep (.refl _)
      refine ⟨out,represented,?_⟩
      simp only [source,terminalIndex,followsRight,bit,if_true]
      rw [activeSame.portWord]
      simp only [out,prepend_portWord,ports,Nat.add_comm 1,List.take_succ_cons,List.cons_append]

end TangoSquared.Paper20261030.SecondaryDecomposition
