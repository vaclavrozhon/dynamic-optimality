import MultiSplay.InterfacePackingRegion
import MultiSplay.ForestSplayGeometry
import MultiSplay.SharedSplayComponents

/-!
# Certified splay components in one actual global history

`Trees` contains only the two physical trees and their embedding in the shared
universe. `Local` adds a rich lazy state. `Packing` certifies all components
together, including every exhausted historical record in a neutral archive.
-/

noncomputable section

namespace MultiSplay.PackedSplay

open Splay.Accounting
open Splay.Interface (Element Parameters)
open SharedSplay
open InterfacePacking (pack)

structure Trees (m : Nat) where
  size : Nat
  comparison : Splay.Tree.BST 0 size
  splay : Splay.Tree.BST 0 size
  element : Element size → Element m
  injective : Function.Injective element

abbrev Local (m : Nat) := Sigma (fun trees : Trees m => Splay.Lazy.State trees.size)

variable {n m : Nat} {params : Parameters}

def Local.checkpoint (component : Local m) : ArticleCheckpoint component.1.size :=
  ⟨component.1.comparison, component.1.splay, component.2⟩

def Local.component (component : Local m) : InterfacePacking.Component m :=
  ⟨component.1.size, component.2.toInterface, component.1.element, component.1.injective⟩

def components (forest : List (Local m)) : List (InterfacePacking.Component m) := forest.map Local.component

def geometry (forest : List (Local m)) : SharedSplay.Forest :=
  forest.map (fun component => ⟨component.1.size, component.checkpoint⟩)

structure Packing (params : Parameters) (forest : List (Local m)) (whole : Splay.Interface.State m) where
  archive : Splay.Interface.State m
  closed : InterfacePacking.Closed archive
  separate : (components forest).Pairwise InterfacePacking.Component.Disjoint
  certified : ∀ component ∈ forest, Certified params component.checkpoint
  equivalent : InterfacePermutation.Equivalent (pack archive (components forest)) whole

def Packing.headFrame {head : Local m} {tail : List (Local m)} {whole : Splay.Interface.State m}
    (packing : Packing params (head :: tail) whole) :
    InterfaceFramedTrace.Framed params head.2.toInterface whole := by
  let frame := InterfacePacking.headFrame packing.archive head.component (components tail)
    packing.closed.valid packing.separate
    (by
      intro component member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (packing.certified original (List.mem_cons_of_mem _ present)).represented.valid.1)
    (fun component _ => packing.closed.passive component.element)
  exact {frame with equivalent :=
    ⟨frame.equivalent.1.trans packing.equivalent.1, frame.equivalent.2.trans packing.equivalent.2⟩}

theorem Packing.valid {forest : List (Local m)} {whole : Splay.Interface.State m}
    (packing : Packing params forest whole) : whole.Valid params := by
  apply packing.equivalent.valid
  apply InterfacePacking.valid packing.archive (components forest) packing.closed.valid packing.separate
  · intro component member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (packing.certified original present).represented.valid.1
  · exact fun component _ => packing.closed.passive component.element

def Packing.reorder {before after : List (Local m)} {whole : Splay.Interface.State m}
    (packing : Packing params before whole) (order : before.Perm after) : Packing params after whole where
  archive := packing.archive
  closed := packing.closed
  separate := (order.map Local.component).pairwise packing.separate (fun h => h.symm)
  certified := fun component member => packing.certified component (order.mem_iff.mpr member)
  equivalent := by
    have same := InterfacePacking.perm packing.archive (order.map Local.component) packing.separate
    exact ⟨same.1.symm.trans packing.equivalent.1, same.2.symm.trans packing.equivalent.2⟩

/-- Replay the actual article macro and reconstruct the complete new packing.
The rest of the forest and the passive historical archive are unchanged. -/
theorem article (before after : ArticleCheckpoint n) (element : Element n → Element m)
    (injective : Function.Injective element) (tail : List (Local m)) (whole : Splay.Interface.State m)
    (packing : Packing params (⟨⟨n, before.comparison, before.splay, element, injective⟩, before.state⟩ :: tail) whole)
    (step : ArticleMacro params before after) (slack depth : Nat) (normal : MacroGeometry.Normal slack depth step) :
    ∃ final : Splay.Interface.State m,
      Nonempty (Packing params (⟨⟨n, after.comparison, after.splay, element, injective⟩, after.state⟩ :: tail) final) ∧
      ∃ segment : Segment params whole final,
        SegmentEvolution slack depth segment
          (⟨n, before⟩ :: geometry tail) (⟨n, after⟩ :: geometry tail) ∧
        segment.splayCost = MacroGeometry.splayCost step ∧
        segment.requests = step.requests.length ∧ segment.rotations = step.rotationCount ∧
        segment.maintenanceCost = 0 := by
  let framed := packing.headFrame
  obtain ⟨run⟩ := FramedSplay.exists_macro step whole framed
  have cert := packing.certified _ (List.mem_cons_self)
  refine ⟨run.final, ?_, .article step cert.unbroken framed run,
    .article step cert.unbroken framed run normal [] (geometry tail), rfl, rfl, rfl, rfl⟩
  refine ⟨⟨packing.archive, packing.closed, ?_, ?_, ?_⟩⟩
  · simpa only [components, List.map_cons, List.pairwise_cons, Local.component,
      InterfacePacking.Component.Disjoint] using packing.separate
  · intro component member
    rcases List.mem_cons.mp member with rfl | member
    · exact cert.after step
    · exact packing.certified component (List.mem_cons_of_mem _ member)
  · have same := run.framed.equivalent
    rw [run.element_eq, run.frame_eq] at same
    exact same

end MultiSplay.PackedSplay
