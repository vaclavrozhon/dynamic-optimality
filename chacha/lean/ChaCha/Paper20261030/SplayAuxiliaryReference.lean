import ChaCha.Paper20261030.SplayAuxiliaryReferenceCore
import ChaCha.Paper20261030.SecondaryDecomposition

/-! # The concrete depth-reference instance of the raw source adapter -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage
open MultiSplay EndpointEncoding ClassicalSwitch Global.Preferred

def secondaryKey (record : SecondaryDecomposition.Cached) : Nat := record.2.1

@[simp] theorem referenceCuts_secondary {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    referenceCuts secondaryKey (SecondaryDecomposition.source reference preference) =
      (separatorReference reference).toRaw := by
  induction reference <;>
    simp_all [SecondaryDecomposition.source,referenceCuts,separatorReference,
      DynamicOptimality.BST.toRaw,secondaryKey]

@[simp] theorem referenceState_secondary {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    referenceState SecondaryDecomposition.followsRight
      (SecondaryDecomposition.source reference preference) =
        routerState (Secondary.decodeDepth reference preference) := by
  induction reference with
  | leaf => rfl
  | node cut ha hb l r ihl ihr =>
      funext owner
      cases owner with
      | nil => rfl
      | cons side rest =>
          cases side
          · exact congrFun ihl rest
          · exact congrFun ihr rest

end ChaCha.Paper20261030.SplayAuxiliary
