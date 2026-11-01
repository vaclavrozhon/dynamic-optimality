import TangoSquared.Paper20261030.TerminalPort
import TangoSquared.Paper20261030.SecondaryAccessRearrangement
import TangoSquared.Paper20261030.AuxiliaryPortSearch

/-! The actual separator search reaches the preferred endpoint's port.
Its gap rank equals the count of right-going preferred reference edges.
After an access update, that endpoint is the requested depth. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

def terminalLeaf (d : Nat) : Source Nat Cached :=
  .leaf d (0,⟨d,((⟨d,d,d⟩,false),true)⟩)

theorem terminalSource_eq {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool) :
    terminalSource followsRight (source reference p) = terminalLeaf (Secondary.decodeDepth reference p).terminal := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
    cases hp : p ⟨a,cut,b⟩ <;>
      simpa only [source,terminalSource,followsRight,hp,Bool.false_eq_true,if_false,if_true,
        Secondary.decodeDepth,PrefRouter.terminal] using (by first | exact ihl | exact ihr)

theorem terminalIndex_rank {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference p).terminal = d) :
    terminalIndex followsRight (source reference p) =
      ((SeparatorPath.word reference p).filter (fun e => decide (e.1 < d))).length := by
  induction reference generalizing d with
  | leaf => rfl
  | @node a b cut ha hb l r ihl ihr =>
    cases hp : p ⟨a,cut,b⟩
    · have ht : (Secondary.decodeDepth l p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,hp,Bool.false_eq_true,if_false] using terminal
      have hm : a ≤ d ∧ d ≤ cut := (Secondary.decodeDepth_mem l p d).mp
        (by rw [← ht]; exact PrefRouter.terminal_mem _)
      have hcut : decide (cut < d) = false := decide_eq_false (by omega)
      simp only [source,terminalIndex,followsRight,hp,Bool.false_eq_true,if_false,
        SeparatorPath.word,List.filter_append,List.filter_cons,List.filter_nil,hcut,List.append_nil]
      exact ihl d ht
    · have ht : (Secondary.decodeDepth r p).terminal = d := by
        simpa only [Secondary.decodeDepth,PrefRouter.terminal,hp,if_true] using terminal
      have hm : cut + 1 ≤ d ∧ d ≤ b := (Secondary.decodeDepth_mem r p d).mp
        (by rw [← ht]; exact PrefRouter.terminal_mem _)
      have hcut : decide (cut < d) = true := decide_eq_true (by omega)
      simp only [source,terminalIndex,followsRight,hp,if_true,
        SeparatorPath.word,List.filter_cons,hcut,List.length_cons,ihr d ht,Nat.add_comm]

theorem represented_terminal_port {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference p).terminal = d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    c.ports (gapIndex d c.core) = terminalLeaf d := by
  have rank : gapIndex d c.core = terminalIndex followsRight (source reference p) := by
    rw [gapIndex_count d c.core c.balanced (represented_ordered reference p c represented),
      represented_word reference p c represented,List.filter_map,List.length_map]
    change ((SeparatorPath.word reference p).filter (fun e => decide (e.1 < d))).length = _
    exact (terminalIndex_rank reference p d terminal).symm
  rw [rank,represented.terminal_port,terminalSource_eq,terminal]

end TangoSquared.Paper20261030.SecondaryDecomposition
