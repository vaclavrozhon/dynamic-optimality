import TangoSquared.Paper20261030.PackedRecordDecoding
import TangoSquared.Paper20261030.SourceStructuralFields

/-! Recognizing the ancestor records that share a projected root.

Every record stores the colors below its logical vertex. An unchanged
subtree's records have masks contained in that subtree's mask. A suppressed
ancestor whose record is stored at the same projected root contributes a
new color outside that mask: at such a stored, suppressed branch the two
child masks are disjoint. Thus a local subset test separates the ancestor
prefix from the subtree records without consulting the logical tree.
-/

namespace TangoSquared.Paper20261030.ColoredStorage

open SourcePointer ProjectionLocal

variable {α ρ C : Type*} [LinearOrder C]

def ColorsCorrect (mask : ρ → Finset C) (color : α → C) : Source α ρ → Prop
  | .leaf key record => mask record = {color key}
  | .fork record l r => mask record = l.support color ∪ r.support color ∧
      ColorsCorrect mask color l ∧ ColorsCorrect mask color r

theorem ColorsCorrect.root {mask : ρ → Finset C} {color : α → C} {source : Source α ρ}
    (correct : ColorsCorrect mask color source) : mask source.rootRecord = source.support color := by
  cases source with
  | leaf => exact correct
  | fork => exact correct.1

theorem ColorsCorrect.focus {mask : ρ → Finset C} {color : α → C}
    (focus : Source α ρ) (outside : List (Frame α ρ)) (correct : ColorsCorrect mask color (plug focus outside)) :
    ColorsCorrect mask color focus := by
  induction outside generalizing focus with
  | nil => exact correct
  | cons frame rest ih =>
    cases frame with
    | left record sibling => exact (ih (.fork record focus sibling) correct).2.1
    | right sibling record => exact (ih (.fork record sibling focus) correct).2.2

theorem ColorsCorrect.subset {mask : ρ → Finset C} {color : α → C} {source : Source α ρ}
    (correct : ColorsCorrect mask color source) {record : ρ} (member : record ∈ source.records) :
    mask record ⊆ source.support color := by
  induction source with
  | leaf key value =>
    have equal : record = value := Multiset.mem_singleton.mp member
    subst record
    change mask value ⊆ {color key}
    rw [correct]
  | fork value l r ihl ihr =>
    simp only [Source.records,Multiset.mem_add,Multiset.mem_singleton] at member
    rcases member with (rfl | left) | right
    · change mask record ⊆ l.support color ∪ r.support color
      rw [correct.1]
    · exact (ihl correct.2.1 left).trans Finset.subset_union_left
    · exact (ihr correct.2.2 right).trans Finset.subset_union_right

theorem annotate_colors_correct {ι : Type*} (identifier : ρ → ι) (color : α → C)
    (parent : Option ι) (source : Source α ρ) :
    ColorsCorrect (fun record => record.2.colors) color (Structural.annotate identifier color parent source) := by
  have support : ∀ (tree : Source α ρ) (p : Option ι),
      (Structural.annotate identifier color p tree).support color = tree.support color := by
    intro tree
    induction tree with
    | leaf => intro p; rfl
    | fork record l r ihl ihr => intro p; simp only [Structural.annotate,Source.support,ihl,ihr]
  induction source generalizing parent with
  | leaf => rfl
  | fork record l r ihl ihr =>
    refine ⟨?_,ihl _,ihr _⟩
    simp only [Structural.fields,Source.support,support]

theorem owned_suppressed_left (color : α → C) (q : C) (focus sibling : Source α ρ)
    (owned : owner color focus sibling = q) (missing : q ∉ sibling.support color) :
    ¬ focus.support color ∪ sibling.support color ⊆ focus.support color := by
  have disjoint := owner_missing_disjoint color q focus sibling owned (Or.inr missing)
  obtain ⟨extra,member⟩ := sibling.support_nonempty color
  intro subset
  have inside := subset (Finset.mem_union_right _ member)
  have both : extra ∈ focus.support color ∩ sibling.support color := Finset.mem_inter.mpr ⟨inside,member⟩
  rw [disjoint] at both
  exact Finset.notMem_empty _ both

theorem owned_suppressed_right (color : α → C) (q : C) (sibling focus : Source α ρ)
    (owned : owner color sibling focus = q) (missing : q ∉ sibling.support color) :
    ¬ sibling.support color ∪ focus.support color ⊆ focus.support color := by
  have disjoint := owner_missing_disjoint color q sibling focus owned (Or.inl missing)
  obtain ⟨extra,member⟩ := sibling.support_nonempty color
  intro subset
  have inside := subset (Finset.mem_union_left _ member)
  have both : extra ∈ sibling.support color ∩ focus.support color := Finset.mem_inter.mpr ⟨member,inside⟩
  rw [disjoint] at both
  exact Finset.notMem_empty _ both

theorem packed_cursor_prefix [DecidableEq α] (mask : ρ → Finset C) (color : α → C) (q : C)
    (source : Source α ρ) (actual : Source α (List ρ)) (packedSource : packed color q source = some actual)
    (outside : List (Frame α ρ)) (correct : ColorsCorrect mask color (plug source outside)) :
    ∃ extras rest,
      packed color q (plug source outside) = some (plug (prepend extras actual) rest) ∧
      rest.map frameShape = LeafPointer.projectedFrames (keepColor color q) (outside.map frameShape) ∧
      ∀ record ∈ extras, ¬ mask record ⊆ source.support color := by
  induction outside generalizing source actual with
  | nil => exact ⟨[],[],by simpa [plug,prepend_nil],rfl,by simp⟩
  | cons frame tail ih =>
    cases frame with
    | left record sibling =>
      let tags : List ρ := if owner color source sibling = q then [record] else []
      cases packedSibling : packed color q sibling with
      | none =>
        have empty := packed_none_shape color q sibling packedSibling
        have combined : packed color q (.fork record source sibling) = some (prepend tags actual) := by
          simp only [packed_fork_decorate,packedSource,packedSibling,ProjectionLocal.join,
            ProjectionLocal.decorate,Option.map_some,prepend,tags]
        obtain ⟨extras,rest,whole,frames,outer⟩ := ih (.fork record source sibling) (prepend tags actual) combined correct
        refine ⟨extras++tags,rest,?_,?_,?_⟩
        · simpa only [plug,prepend_prepend] using whole
        · simpa only [List.map_cons,frameShape,LeafPointer.projectedFrames,empty,if_true] using frames
        · intro entry member
          rcases List.mem_append.mp member with inherited | added
          · exact fun subset => outer entry inherited (subset.trans Finset.subset_union_left)
          · have here := ColorsCorrect.focus (.fork record source sibling) tail correct
            by_cases owned : owner color source sibling = q
            · have same : entry = record := by simpa only [tags,if_pos owned,List.mem_singleton] using added
              subst entry
              rw [here.1]
              exact owned_suppressed_left color q source sibling owned ((packed_none_iff color q sibling).mp packedSibling)
            · simp only [tags,if_neg owned,List.not_mem_nil] at added
      | some sibling' =>
        have shape := packed_shape color q sibling packedSibling
        have nonempty : sibling.shape.prune (keepColor color q) ≠ .empty := by rw [← shape]; exact source_nonempty sibling'
        have combined : packed color q (.fork record source sibling) = some (.fork tags actual sibling') := by
          simp only [packed_fork_decorate,packedSource,packedSibling,ProjectionLocal.join,
            ProjectionLocal.decorate,Option.map_some,Source.rootRecord,Source.setRoot,List.append_nil,tags]
        obtain ⟨extras,rest,whole,frames,_⟩ := ih (.fork record source sibling) (.fork tags actual sibling') combined correct
        refine ⟨[],.left (extras++tags) sibling'::rest,?_,?_,by simp⟩
        · rw [prepend_nil]
          simpa only [plug,prepend,Source.rootRecord,Source.setRoot] using whole
        · simp only [List.map_cons,frameShape,LeafPointer.projectedFrames,nonempty,if_false,shape,frames]
    | right sibling record =>
      let tags : List ρ := if owner color sibling source = q then [record] else []
      cases packedSibling : packed color q sibling with
      | none =>
        have empty := packed_none_shape color q sibling packedSibling
        have combined : packed color q (.fork record sibling source) = some (prepend tags actual) := by
          simp only [packed_fork_decorate,packedSource,packedSibling,ProjectionLocal.join,
            ProjectionLocal.decorate,Option.map_some,prepend,tags]
        obtain ⟨extras,rest,whole,frames,outer⟩ := ih (.fork record sibling source) (prepend tags actual) combined correct
        refine ⟨extras++tags,rest,?_,?_,?_⟩
        · simpa only [plug,prepend_prepend] using whole
        · simpa only [List.map_cons,frameShape,LeafPointer.projectedFrames,empty,if_true] using frames
        · intro entry member
          rcases List.mem_append.mp member with inherited | added
          · exact fun subset => outer entry inherited (subset.trans Finset.subset_union_right)
          · have here := ColorsCorrect.focus (.fork record sibling source) tail correct
            by_cases owned : owner color sibling source = q
            · have same : entry = record := by simpa only [tags,if_pos owned,List.mem_singleton] using added
              subst entry
              rw [here.1]
              exact owned_suppressed_right color q sibling source owned ((packed_none_iff color q sibling).mp packedSibling)
            · simp only [tags,if_neg owned,List.not_mem_nil] at added
      | some sibling' =>
        have shape := packed_shape color q sibling packedSibling
        have nonempty : sibling.shape.prune (keepColor color q) ≠ .empty := by rw [← shape]; exact source_nonempty sibling'
        have combined : packed color q (.fork record sibling source) = some (.fork tags sibling' actual) := by
          simp only [packed_fork_decorate,packedSource,packedSibling,ProjectionLocal.join,
            ProjectionLocal.decorate,Option.map_some,Source.rootRecord,Source.setRoot,List.append_nil,tags]
        obtain ⟨extras,rest,whole,frames,_⟩ := ih (.fork record sibling source) (.fork tags sibling' actual) combined correct
        refine ⟨[],.right sibling' (extras++tags)::rest,?_,?_,by simp⟩
        · rw [prepend_nil]
          simpa only [plug,prepend,Source.rootRecord,Source.setRoot] using whole
        · simp only [List.map_cons,frameShape,LeafPointer.projectedFrames,nonempty,if_false,shape,frames]

end TangoSquared.Paper20261030.ColoredStorage
