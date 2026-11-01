import TangoSquared.Paper20261030.TerminalRank
import TangoSquared.Paper20261030.LeafVisit

/-!
# Reaching and reading the requested secondary terminal

After the preference-update phase, the root auxiliary's selected endpoint
is the request. A physical separator search reaches its actual terminal
port, reads that leaf, and retraces the path. Opening and closing the entry
marker are included in the cost. This completes the source-trace service
witness; bounded observed departure/boundary selection remains separate.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem visit_terminal {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference p).terminal = d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    SourcePointer.VisitsLeaf d (closed c) (closed c) (12 * Nat.clog 2 (c.core.size + 1) + 5) := by
  intro ancestors
  obtain ⟨hc,hp⟩ := represented.invariant
  obtain ⟨openReads,openCost,opened,openBound⟩ := open_charged c hc hp ancestors
  obtain ⟨atLeaf,searchReads,searchCost,searched,focus,whole,searchBound⟩ :=
    search_port_log d c.core c.balanced c.ports 0 ancestors
  have atTerminal : atLeaf.focus = terminalLeaf d := by
    rw [Nat.zero_add,represented_terminal_port reference p d terminal c represented] at focus
    exact focus
  obtain ⟨backReads,back⟩ := searched.reverse
  obtain ⟨closeReads,closeCost,closedTrace,closeBound⟩ := close_charged c ancestors
  have first := opened.append searched
  have last := SourcePointer.Trace.read (back.append closedTrace)
  refine ⟨atLeaf,(0,⟨d,((⟨d,d,d⟩,false),true)⟩),openReads ++ searchReads,backReads ++ closeReads,
    openCost + searchCost,searchCost + closeCost + 1,first,atTerminal,?_,by omega⟩
  simpa only [atTerminal,terminalLeaf,Source.rootRecord] using last

theorem access_visits_leaf {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (request : Nat) (valid : a ≤ request ∧ request ≤ b)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Secondary.intervalUpdate request p)) out ∧
      SourcePointer.VisitsLeaf request (closed c) (closed out)
        (((Secondary.decodeDepth reference p).accessFlips request + 1) * repairBound reference) := by
  obtain ⟨out,hout,rearranged⟩ := access_rearrangement reference p request c represented
  have endpoint : (Secondary.decodeDepth reference (Secondary.intervalUpdate request p)).terminal = request := by
    rw [Secondary.decodeDepth_access]
    exact PrefRouter.terminal_access _ _ ((Secondary.decodeDepth_mem reference p request).mpr valid)
  have visited := visit_terminal reference (Secondary.intervalUpdate request p) request endpoint out hout
  refine ⟨out,hout,(visited.prepend rearranged).mono ?_⟩
  rw [Nat.add_mul,Nat.one_mul]
  apply Nat.add_le_add_left
  have hsize := represented_size reference (Secondary.intervalUpdate request p) out hout
  have hlog := Nat.clog_monotone 2 (Nat.add_le_add_right hsize 1)
  unfold repairBound
  omega

end TangoSquared.Paper20261030.SecondaryDecomposition
