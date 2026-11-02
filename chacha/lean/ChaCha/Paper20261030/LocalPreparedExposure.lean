import ChaCha.Paper20261030.LocalAdjacentExposure
import ChaCha.Paper20261030.SuffixDecomposition
import ChaCha.Paper20261030.PreparedSplitWitnesses

set_option autoImplicit false

/-!
# Actual preparation of a represented secondary boundary

Prepared endpoints imply that the needed separators occur in the root
auxiliary. The existing local split controllers expose the exact terminal
and its lower/upper fragments. The caller does not supply successful
searches or a trace oracle. The zero-depth case uses the sentinel theorem
with the full suffix at the minimum reference depth.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.PreparedExposureController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage SourcePointer Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition SourceLocalProgram

theorem active {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = d)
    (lower : a < d) (upper : d < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component) (outside) :
    ∃ (left right : AuxiliaryComponent Nat Nat (Tagged Payload)) (low high : Cached),
      low.2.1 = d-1 ∧ high.2.1 = d ∧
      Clean left.core ∧ MarkedPorts left ∧ Clean right.core ∧ MarkedPorts right ∧
      PreparedSplitWitnesses.Active component d left right low high ∧
      ∃ reads cost, Run (AdjacentExposureController.program (d-1)) (.first .start) ⟨closed component,outside⟩ .done
        ⟨.fork low left.tree (.fork high (terminalLeaf d) right.tree),outside⟩ reads cost ∧
        cost ≤ 80220*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+4 := by
  have ordered := represented_ordered reference preferences component represented
  obtain ⟨clean,marked⟩ := represented.invariant
  have fl := prepared_lower_found reference preferences d terminal lower component represented
  have fu := prepared_upper_found reference preferences d terminal upper component represented
  have next : d-1+1 = d := by omega
  have fh : searchResult (d-1+1) (cutRight component (d-1) fl).core = true := by
    rw [next]
    exact higher_found_right component ordered (d-1) d (by omega) fl fu
  obtain ⟨reads,cost,actual,bound⟩ := AdjacentExposureController.expose component ordered clean marked (d-1) fl fh outside
  simp only [next] at actual
  rw [represented_terminal_port reference preferences d terminal component represented] at actual
  have splitValue (k l : Nat) (same : k = l)
      (hk : searchResult k (cutRight component (d-1) fl).core = true)
      (hl : searchResult l (cutRight component (d-1) fl).core = true) :
      (splitAt k (cutRight component (d-1) fl).core (cutRight component (d-1) fl).balanced hk).value =
      (splitAt l (cutRight component (d-1) fl).core (cutRight component (d-1) fl).balanced hl).value := by
    subst l
    rfl
  rw [splitValue (d-1+1) d next fh (by simpa only [next] using fh)] at actual
  refine ⟨cutLeft component (d-1) fl,cutRight (cutRight component (d-1) fl) d (by simpa only [next] using fh),
    (component.core.size,⟨d-1,(splitAt (d-1) component.core component.balanced fl).value⟩),
    ((cutRight component (d-1) fl).core.size,
      ⟨d,(splitAt d (cutRight component (d-1) fl).core (cutRight component (d-1) fl).balanced (by simpa only [next] using fh)).value⟩),
    rfl,rfl,(clean_split component clean (d-1) fl).2.1,marked_cutLeft component marked (d-1) fl,
    (clean_split _ (clean_split component clean (d-1) fl).2.2 d _).2.2,
    marked_cutRight _ (marked_cutRight component marked (d-1) fl) d _,
    ⟨fl,by simpa only [next] using fh,rfl,rfl,rfl,rfl⟩,reads,cost,?_,?_⟩
  · exact actual
  · have size := represented_size reference preferences component represented
    have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
    omega

theorem sentinel {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (terminal : (Secondary.decodeDepth reference preferences).terminal = d)
    (upper : d < b) (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference preferences d valid) component) (outside) :
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (high : Cached),
      high.2.1 = d ∧ Clean right.core ∧ MarkedPorts right ∧
      PreparedSplitWitnesses.Sentinel component d right high ∧
      ∃ reads cost, Run (OpenSplitController.program d) .start ⟨closed component,outside⟩ .done
        ⟨.fork high (terminalLeaf d) right.tree,outside⟩ reads cost ∧
        cost ≤ 40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2 := by
  have ordered := represented_suffix_ordered reference preferences d valid terminal component represented
  have minimum := represented_suffix_minimum reference preferences d valid terminal component represented
  have found := represented_suffix_boundary_found reference preferences d valid terminal upper component represented
  obtain ⟨clean,marked⟩ := represented.invariant
  obtain ⟨reads,cost,actual,bound⟩ := OpenSplitController.split component clean marked d found outside
  have empty := minimum_left_empty component ordered d found minimum
  have left : (cutLeft component d found).tree = terminalLeaf d := by
    unfold AuxiliaryComponent.tree
    rw [empty]
    simp only [Auxiliary.recordTree,GapSource.encode,cutLeft]
    exact represented_sentinel_port reference preferences d valid terminal component represented
  rw [left] at actual
  refine ⟨cutRight component d found,(component.core.size,⟨d,(splitAt d component.core component.balanced found).value⟩),rfl,
    (clean_split component clean d found).2.2,marked_cutRight component marked d found,⟨found,rfl,rfl⟩,reads,cost,actual,?_⟩
  have size := represented_suffix_size reference preferences d valid component represented
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  omega

end ChaCha.Paper20261030.SecondaryDecomposition.PreparedExposureController
