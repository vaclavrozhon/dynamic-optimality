import ChaCha.Paper20261030.CanonicalHeadWingViews
import ChaCha.Paper20261030.SourceFingerExtension

set_option autoImplicit false

/-! The boundary child of an exposed active wing lies at a path computed
from its two block-presence bits. The component connector contributes at
most two further edges. These paths contain no information from an
unobserved source tree. -/

namespace ChaCha.Paper20261030.HeadBoundaryRoute

open ColoredStorage SourcePointer SourcePositions Structural PhysicalPacketStaging
open CanonicalHeadWingViews MixedHeadInputView PacketLayers.Representation

variable {α β ρ ι : Type*}

def wingPath (reverse headPresent tailPresent : Bool) : List Bool :=
  (if headPresent then [!reverse] else []) ++ (if tailPresent then [reverse] else [])

def path (leftSide oppositePresent headPresent tailPresent : Bool) : List Bool :=
  (if leftSide then (if oppositePresent then [false,false] else [false]) else [true]) ++
    wingPath (!leftSide) headPresent tailPresent

theorem path_length (leftSide oppositePresent headPresent tailPresent : Bool) :
    (path leftSide oppositePresent headPresent tailPresent).length ≤ 4 := by
  cases leftSide <;> cases oppositePresent <;> cases headPresent <;> cases tailPresent <;> decide

theorem path_nonempty (leftSide oppositePresent headPresent tailPresent : Bool) :
    path leftSide oppositePresent headPresent tailPresent ≠ [] := by
  cases leftSide <;> cases oppositePresent <;> cases headPresent <;> cases tailPresent <;> decide

theorem wing (reverse : Bool) (lower upper : JoinFields ι)
    (attachmentId : ι) (attachmentFields : Fields ι Unit)
    (low high : List ρ) (terminal : ρ)
    (headPart tail : Physical β α ρ ι) (child : Source β (PacketLayers.Context.Cell α ρ ι)) :
    ∃ tree current packet,
      activeView reverse true lower upper attachmentId attachmentFields low high terminal headPart tail (some child) = some tree ∧
      locate tree (wingPath reverse headPart.isSome tail.isSome) = some current ∧
      current.focus = child.setRoot (child.rootRecord.1,some packet :: none :: child.rootRecord.2) := by
  cases reverse <;> cases headPart <;> cases tail <;> cases child <;>
    simp [activeView,orientedJoin,MixedHeadInputView.join,physicalJoin,attach,addRoot,
      PhysicalPacketStaging.Context.prependLogical,wingPath,locate,descend,SourceLocalProgram.navigate,
      Source.setRoot,Source.rootRecord]

def assembledView (leftSide : Bool) (first root : ι) (selected opposite : Physical β α ρ ι)
    (bottom : Source β (PacketLayers.Context.Cell α ρ ι)) : Physical β α ρ ι :=
  if leftSide then physicalPrimaryJoin root (physicalPrimaryJoin first selected (some bottom)) opposite
  else physicalPrimaryJoin root (physicalPrimaryJoin first opposite (some bottom)) selected

theorem component (leftSide : Bool) (first root : ι) (lower upper : JoinFields ι)
    (attachmentId : ι) (attachmentFields : Fields ι Unit)
    (low high : List ρ) (terminal : ρ)
    (headPart tail opposite : Physical β α ρ ι) (bottom child : Source β (PacketLayers.Context.Cell α ρ ι)) :
    ∃ tree current packet,
      assembledView leftSide first root
        (activeView (!leftSide) true lower upper attachmentId attachmentFields low high terminal headPart tail (some child))
        opposite bottom = some tree ∧
      locate tree (path leftSide opposite.isSome headPart.isSome tail.isSome) = some current ∧
      current.focus = child.setRoot (child.rootRecord.1,some packet :: none :: child.rootRecord.2) := by
  obtain ⟨selected,inside,packet,view,walk,payload⟩ := wing (!leftSide) lower upper attachmentId attachmentFields low high terminal headPart tail child
  rw [view]
  cases leftSide with
  | false =>
    cases opposite with
    | none =>
      exact ⟨_,_,packet,rfl,locate_right walk (root,[]) bottom,payload⟩
    | some other =>
      exact ⟨_,_,packet,rfl,locate_right walk (root,[]) (.fork (first,[]) other bottom),payload⟩
  | true =>
    cases opposite with
    | none =>
      exact ⟨_,_,packet,rfl,locate_left walk (first,[]) bottom,payload⟩
    | some other =>
      exact ⟨_,_,packet,rfl,locate_left (locate_left walk (first,[]) bottom) (root,[]) other,payload⟩

end ChaCha.Paper20261030.HeadBoundaryRoute
