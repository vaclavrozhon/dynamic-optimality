import TangoSquared.Paper20261030.LocalPreparedRestore

set_option autoImplicit false

/-! Exact auxiliary split witnesses retained by boundary preparation.
They identify the exposed records and fragments with the actual balanced
cuts. Consequently restoring the transferred fragments proves the
prescribed secondary preferences, as well as balance. These are proof
witnesses; the runtime restoration controller reads its separators. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.PreparedSplitWitnesses

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage SourcePointer Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition SourceLocalProgram

structure Active (component : AuxiliaryComponent Nat Nat (Tagged Payload)) (d : Nat)
    (left right : AuxiliaryComponent Nat Nat (Tagged Payload)) (low high : Cached) : Prop where
  lowFound : searchResult (d-1) component.core = true
  highFound : searchResult d (cutRight component (d-1) lowFound).core = true
  left_eq : left = cutLeft component (d-1) lowFound
  right_eq : right = cutRight (cutRight component (d-1) lowFound) d highFound
  low_eq : low = (component.core.size,⟨d-1,(splitAt (d-1) component.core component.balanced lowFound).value⟩)
  high_eq : high = ((cutRight component (d-1) lowFound).core.size,
    ⟨d,(splitAt d (cutRight component (d-1) lowFound).core (cutRight component (d-1) lowFound).balanced highFound).value⟩)

structure Sentinel (component : AuxiliaryComponent Nat Nat (Tagged Payload)) (d : Nat)
    (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (high : Cached) : Prop where
  found : searchResult d component.core = true
  right_eq : right = cutRight component d found
  high_eq : high = (component.core.size,⟨d,(splitAt d component.core component.balanced found).value⟩)

theorem active_restore {a b : Nat} (reference : DepthTree a b) (oldPreferences incomingPreferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (lower : a < d)
    (preparedOld : (Secondary.decodeDepth reference oldPreferences).terminal = d)
    (preparedIncoming : (Secondary.decodeDepth reference incomingPreferences).terminal = d)
    (old incoming left oldRight incomingRight : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (source reference oldPreferences) old)
    (incomingRep : Represents followsRight (suffixSource reference incomingPreferences d valid) incoming)
    (low oldHigh incomingHigh : Cached)
    (active : Active old d left oldRight low oldHigh)
    (sentinel : Sentinel incoming d incomingRight incomingHigh) (outside) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Secondary.spliceBits d oldPreferences incomingPreferences)) out ∧
      ∃ reads cost, Run (HeadRestoreController.program true) (HeadRestoreController.initial true)
        ⟨.fork low left.tree (.fork incomingHigh (terminalLeaf d) incomingRight.tree),outside⟩ .done
        ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 6300*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+620 := by
  rcases active with ⟨fl,fh,rfl,rfl,rfl,rfl⟩
  rcases sentinel with ⟨fi,rfl,rfl⟩
  exact PreparedRestoreController.active reference oldPreferences incomingPreferences d valid lower preparedOld preparedIncoming
    old incoming oldRep incomingRep fl fi outside

theorem dormant_restore {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (lower : a < d)
    (prepared : (Secondary.decodeDepth reference preferences).terminal = d)
    (old left right : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (source reference preferences) old)
    (low high : Cached) (active : Active old d left right low high) (outside) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (suffixSource reference preferences d valid) out ∧
      ∃ reads cost, Run (HeadRestoreController.program false) (HeadRestoreController.initial false)
        ⟨.fork high (terminalLeaf d) right.tree,outside⟩ .done ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310 := by
  rcases active with ⟨fl,fh,rfl,rfl,rfl,rfl⟩
  have suffixRep := prepared_cutRight_represents reference preferences d valid prepared lower old oldRep fl
  obtain ⟨out,_,represented,reads,cost,actual,bound⟩ := PreparedRestoreController.sentinel reference preferences d valid prepared
    (cutRight old (d-1) fl) suffixRep fh outside
  exact ⟨out,represented,reads,cost,actual,bound⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.PreparedSplitWitnesses
