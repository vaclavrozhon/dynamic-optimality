import ChaCha.Paper20261030.PackedNavigation

/-!
# The physical location of an active source cursor

The packed context correspondence now also identifies the cursor's
routing position. It is therefore the same cursor as the active/parked
navigation representation, rather than an existentially chosen location
elsewhere in the packed tree.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer ProjectionLocal RouterProjection

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

theorem packed_none_shape (color : α → C) (q : C) (source : Source α ρ)
    (h : packed color q source = none) :
    source.shape.prune (keepColor color q) = .empty := by
  have hf : Router.Full (pack color q source).shape := by
    rw [pack_shape]
    exact Router.full_prune _ _
  have he := (pack color q source).toSource_roundtrip hf
  change storedOption (packed color q source) = _ at he
  rw [h] at he
  have hs := congrArg Stored.shape he.symm
  change source.shape.prune (fun key => decide (color key = q)) = .empty
  simpa only [storedOption,Stored.shape,pack_shape] using hs

theorem packed_fork_decorate (color : α → C) (q : C) (record : ρ)
    (l r : Source α ρ) :
    packed color q (.fork record l r) =
      ProjectionLocal.decorate (if owner color l r = q then [record] else [])
        (ProjectionLocal.join (packed color q l) (packed color q r)) := by
  rw [packed_fork]
  by_cases ho : owner color l r = q
  · simp [ho,ProjectionLocal.attach,ProjectionLocal.decorate]
  · simp only [ho,decide_false,ProjectionLocal.attach,if_false,Bool.false_eq_true,
      ProjectionLocal.decorate,List.nil_append]
    cases ProjectionLocal.join (packed color q l) (packed color q r) with
    | none => rfl
    | some t => cases t <;> rfl

theorem packed_cursor_context (color : α → C) (q : C)
    {s t : Source α ρ} (hs : s.support color = t.support color)
    {a b : Source α (List ρ)}
    (ha : packed color q s = some a) (hb : packed color q t = some b)
    (ancestors : List (Frame α ρ)) :
    ∃ (extras : List ρ) (rest : List (Frame α (List ρ))),
      packed color q (plug s ancestors) = some (plug (prepend extras a) rest) ∧
      packed color q (plug t ancestors) = some (plug (prepend extras b) rest) ∧
      rest.map frameShape = LeafPointer.projectedFrames (keepColor color q)
        (ancestors.map frameShape) := by
  induction ancestors generalizing s t a b with
  | nil => exact ⟨[],[],by simpa [plug,prepend_nil],by simpa [plug,prepend_nil],rfl⟩
  | cons frame tail ih =>
    cases frame with
    | left record sibling =>
      let tags : List ρ := if owner color s sibling = q then [record] else []
      have he := owner_congr color hs (rfl (a := sibling.support color))
      cases hp : packed color q sibling with
      | none =>
        have hpn := packed_none_shape color q sibling hp
        have hsa : packed color q (.fork record s sibling) = some (prepend tags a) := by
          simp only [packed_fork_decorate,ha,hp,ProjectionLocal.join,
            ProjectionLocal.decorate,Option.map_some,prepend,tags]
        have htb : packed color q (.fork record t sibling) = some (prepend tags b) := by
          simp only [packed_fork_decorate,hb,hp,ProjectionLocal.join,← he,
            ProjectionLocal.decorate,Option.map_some,prepend,tags]
        obtain ⟨extras,rest,hl,hr,hframes⟩ := ih
          (by simp only [Source.support,hs]) hsa htb
        refine ⟨extras ++ tags,rest,?_,?_,?_⟩
        · simpa only [plug,prepend_prepend] using hl
        · simpa only [plug,prepend_prepend] using hr
        · simpa only [List.map_cons,frameShape,LeafPointer.projectedFrames,hpn,if_true] using hframes
      | some sibling' =>
        have hps := packed_shape color q sibling hp
        have hpn : sibling.shape.prune (keepColor color q) ≠ .empty := by
          rw [← hps]; exact source_nonempty sibling'
        have hsa : packed color q (.fork record s sibling) = some (.fork tags a sibling') := by
          simp only [packed_fork_decorate,ha,hp,ProjectionLocal.join,
            ProjectionLocal.decorate,Option.map_some,Source.rootRecord,Source.setRoot,List.append_nil,tags]
        have htb : packed color q (.fork record t sibling) = some (.fork tags b sibling') := by
          simp only [packed_fork_decorate,hb,hp,ProjectionLocal.join,← he,
            ProjectionLocal.decorate,Option.map_some,Source.rootRecord,Source.setRoot,List.append_nil,tags]
        obtain ⟨extras,rest,hl,hr,hframes⟩ := ih
          (by simp only [Source.support,hs]) hsa htb
        refine ⟨[],.left (extras ++ tags) sibling' :: rest,?_,?_,?_⟩
        · rw [prepend_nil]
          simpa only [plug,prepend,Source.rootRecord,Source.setRoot] using hl
        · rw [prepend_nil]
          simpa only [plug,prepend,Source.rootRecord,Source.setRoot] using hr
        · simp only [List.map_cons,frameShape,LeafPointer.projectedFrames,hpn,if_false,hps,hframes]
    | right sibling record =>
      let tags : List ρ := if owner color sibling s = q then [record] else []
      have he := owner_congr color (rfl (a := sibling.support color)) hs
      cases hp : packed color q sibling with
      | none =>
        have hpn := packed_none_shape color q sibling hp
        have hsa : packed color q (.fork record sibling s) = some (prepend tags a) := by
          simp only [packed_fork_decorate,ha,hp,ProjectionLocal.join,
            ProjectionLocal.decorate,Option.map_some,prepend,tags]
        have htb : packed color q (.fork record sibling t) = some (prepend tags b) := by
          simp only [packed_fork_decorate,hb,hp,ProjectionLocal.join,← he,
            ProjectionLocal.decorate,Option.map_some,prepend,tags]
        obtain ⟨extras,rest,hl,hr,hframes⟩ := ih
          (by simp only [Source.support,hs]) hsa htb
        refine ⟨extras ++ tags,rest,?_,?_,?_⟩
        · simpa only [plug,prepend_prepend] using hl
        · simpa only [plug,prepend_prepend] using hr
        · simpa only [List.map_cons,frameShape,LeafPointer.projectedFrames,hpn,if_true] using hframes
      | some sibling' =>
        have hps := packed_shape color q sibling hp
        have hpn : sibling.shape.prune (keepColor color q) ≠ .empty := by
          rw [← hps]; exact source_nonempty sibling'
        have hsa : packed color q (.fork record sibling s) = some (.fork tags sibling' a) := by
          simp only [packed_fork_decorate,ha,hp,ProjectionLocal.join,
            ProjectionLocal.decorate,Option.map_some,Source.rootRecord,Source.setRoot,List.append_nil,tags]
        have htb : packed color q (.fork record sibling t) = some (.fork tags sibling' b) := by
          simp only [packed_fork_decorate,hb,hp,ProjectionLocal.join,← he,
            ProjectionLocal.decorate,Option.map_some,Source.rootRecord,Source.setRoot,List.append_nil,tags]
        obtain ⟨extras,rest,hl,hr,hframes⟩ := ih
          (by simp only [Source.support,hs]) hsa htb
        refine ⟨[],.right sibling' (extras ++ tags) :: rest,?_,?_,?_⟩
        · rw [prepend_nil]
          simpa only [plug,prepend,Source.rootRecord,Source.setRoot] using hl
        · rw [prepend_nil]
          simpa only [plug,prepend,Source.rootRecord,Source.setRoot] using hr
        · simp only [List.map_cons,frameShape,LeafPointer.projectedFrames,hpn,if_false,hps,hframes]

theorem represents_of_context (color : α → C) (q : C) (source : Source α ρ)
    (ancestors : List (Frame α ρ)) {actual : Source α (List ρ)}
    (ha : packed color q source = some actual) (extras : List ρ)
    (rest : List (Frame α (List ρ)))
    (ht : packed color q (plug source ancestors) = some (plug (prepend extras actual) rest))
    (hf : rest.map frameShape = LeafPointer.projectedFrames (keepColor color q)
      (ancestors.map frameShape)) :
    Represents color q ⟨source,ancestors⟩ ⟨prepend extras actual,rest⟩ := by
  have hs := packed_shape color q source ha
  have hn : source.shape.prune (keepColor color q) ≠ .empty := by
    rw [← hs]; exact source_nonempty actual
  refine ⟨ht,?_⟩
  simp only [LeafPointer.project,cursorShape,hn,if_false,prepend,source_setRoot_shape,hf,hs]

end ChaCha.Paper20261030.ColoredStorage
