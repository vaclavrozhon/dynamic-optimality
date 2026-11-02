import ChaCha.Paper20261030.LocalAlignedContextReassembly
import ChaCha.Paper20261030.ObservedHeadBlueprint

/-! The actual observed head prefixes satisfy the neutrality condition
of the identifier-aligned reassembly controller. Logical records become
temporary markers; stored virtual headers and delimiters are retained as
raw bottom packets. Neither requires another vertex's physical id.
-/

namespace ChaCha.Paper20261030.PacketAlignment

open ColoredStorage SourcePointer Structural HeadBoundary HeadBlocks PhysicalPacketStaging

variable {α ρ ι η : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem neutral_nil (markerId : ι) : Neutral (α := α) (ρ := ρ) markerId [] := by
  intro vertexId entry member
  cases member

theorem neutral_append (markerId : ι) (first last : Packet α ρ ι)
    (hf : Neutral markerId first) (hl : Neutral markerId last) : Neutral markerId (first++last) :=
  fun vertexId => append markerId vertexId first last (hf vertexId) (hl vertexId)

def markerValue (markerId : ι) (record : ρ) : Datum α ρ ι := .real ((markerId,[record]),placeholder)

theorem connector_neutral (markerId : ι) (q : Option Bool) (record : HeadBoundary.Record ρ η (Option Bool)) :
    Neutral markerId (ObservedHeadBlueprint.connector (markerValue (α := α) markerId) q record) := by
  unfold ObservedHeadBlueprint.connector
  split
  · exact neutral_nil markerId
  · split
    · exact markers markerId [record]
    · exact neutral_nil markerId

def ActiveNeutral (markerId : ι) (records : ActiveRecords (Option (Datum α ρ ι))) : Prop :=
  Neutral markerId records.lowerLeft ∧ Neutral markerId records.lowerRight ∧
  Neutral markerId records.upperLeft ∧ Neutral markerId records.upperRight ∧
  Neutral markerId records.bottom ∧ Neutral markerId records.attachment

def DormantNeutral (markerId : ι) (records : DormantRecords (Option (Datum α ρ ι))) : Prop :=
  Neutral markerId records.left ∧ Neutral markerId records.right ∧ Neutral markerId records.bottom

theorem active_neutral (markerId : ι) (low high terminal : HeadBoundary.Record ρ η (Option Bool))
    (bottom : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) (bottomNeutral : Neutral markerId bottom) :
    ActiveNeutral markerId (ObservedHeadBlueprint.active (markerValue markerId) low high terminal bottom) := by
  refine ⟨connector_neutral markerId _ low,connector_neutral markerId _ low,
    connector_neutral markerId _ high,connector_neutral markerId _ high,bottomNeutral,?_⟩
  intro vertexId entry member
  simp only [ObservedHeadBlueprint.active,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl rfl
  · trivial

theorem dormant_neutral (markerId : ι) (high : HeadBoundary.Record ρ η (Option Bool))
    (bottom : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) (bottomNeutral : Neutral markerId bottom) :
    DormantNeutral markerId (ObservedHeadBlueprint.dormant (markerValue markerId) high bottom) :=
  ⟨connector_neutral markerId _ high,connector_neutral markerId _ high,bottomNeutral⟩

private theorem leaf_neutral (markerId : ι) (key : Fin 8) :
    SourceRecordPredicate.Holds (Neutral (α := α) (ρ := ρ) markerId) (.leaf key []) :=
  (SourceRecordPredicate.leaf _ _ _).mpr (neutral_nil markerId)

private theorem join_neutral (markerId : ι) (left right : Source (Fin 8) (Packet α ρ ι))
    (hl : SourceRecordPredicate.Holds (Neutral markerId) left)
    (hr : SourceRecordPredicate.Holds (Neutral markerId) right) :
    SourceRecordPredicate.Holds (Neutral markerId) (.fork [] left right) :=
  (SourceRecordPredicate.fork _ _ _ _).mpr ⟨neutral_nil markerId,hl,hr⟩

private theorem decorate_neutral (markerId : ι) (records : Packet α ρ ι) (context : Source (Fin 8) (Packet α ρ ι))
    (hr : Neutral markerId records) (hc : SourceRecordPredicate.Holds (Neutral markerId) context) :
    SourceRecordPredicate.Holds (Neutral markerId) (ExposedLocal.decorateContext records context) :=
  SourceRecordPredicate.setRoot _ _ _ hc (neutral_append markerId _ _ hr (SourceRecordPredicate.root _ _ hc))

theorem dormant_context_neutral (markerId : ι) (l b r : Fin 8)
    (records : DormantRecords (Option (Datum α ρ ι))) (neutral : DormantNeutral markerId records) :
    SourceRecordPredicate.Holds (Neutral markerId) (ExposedLocal.dormantContext l b r records) :=
  join_neutral markerId _ _
    (join_neutral markerId _ _
      (decorate_neutral markerId _ _ neutral.1 (leaf_neutral markerId l))
      (decorate_neutral markerId _ _ neutral.2.2 (leaf_neutral markerId b)))
    (decorate_neutral markerId _ _ neutral.2.1 (leaf_neutral markerId r))

theorem active_context_neutral (markerId : ι) (l r tl b tr : Fin 8)
    (boundary : Source (Fin 8) (Packet α ρ ι)) (boundaryNeutral : SourceRecordPredicate.Holds (Neutral markerId) boundary)
    (direction : Bool) (records : ActiveRecords (Option (Datum α ρ ι))) (neutral : ActiveNeutral markerId records) :
    SourceRecordPredicate.Holds (Neutral markerId) (ExposedLocal.activeContext l r tl b tr boundary direction records) := by
  have child := decorate_neutral markerId records.attachment boundary neutral.2.2.2.2.2 boundaryNeutral
  have left : SourceRecordPredicate.Holds (Neutral markerId)
      (if direction then .fork [] (ExposedLocal.decorateContext records.attachment boundary) (.leaf tl []) else .leaf tl []) := by
    cases direction
    · exact leaf_neutral markerId tl
    · exact join_neutral markerId _ _ child (leaf_neutral markerId tl)
  have right : SourceRecordPredicate.Holds (Neutral markerId)
      (if direction then .leaf tr [] else .fork [] (.leaf tr []) (ExposedLocal.decorateContext records.attachment boundary)) := by
    cases direction
    · exact join_neutral markerId _ _ (leaf_neutral markerId tr) child
    · exact leaf_neutral markerId tr
  exact join_neutral markerId _ _
    (join_neutral markerId _ _
      (decorate_neutral markerId _ _ neutral.1
        (join_neutral markerId _ _ (leaf_neutral markerId l) (decorate_neutral markerId _ _ neutral.2.2.1 left)))
      (decorate_neutral markerId _ _ neutral.2.2.2.2.1 (leaf_neutral markerId b)))
    (decorate_neutral markerId _ _ neutral.2.1
      (join_neutral markerId _ _ (decorate_neutral markerId _ _ neutral.2.2.2.1 right) (leaf_neutral markerId r)))

theorem after_neutral (markerId : ι) (direction : Bool) (records : Records ρ η (Option Bool))
    (activeHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (activeValid : Neutral markerId activeHeader) (dormantValid : Neutral markerId dormantHeader) :
    SourceRecordPredicate.Holds (Neutral markerId)
      (ObservedHeadBlueprint.afterContext (markerValue markerId) direction records activeHeader dormantHeader) :=
  active_context_neutral markerId 0 7 4 5 6 _
    (dormant_context_neutral markerId 1 2 3 _ (dormant_neutral markerId records.oldHigh dormantHeader dormantValid))
    (!direction) _ (active_neutral markerId records.low records.incomingHigh records.incomingTerminal activeHeader activeValid)

/-- The head controller's actual scalar/record inputs determine the
instruction list. The block trees appear only in this representation
theorem, and alignment is maintained on the complete physical tree. -/
theorem head_reassemble {β F : Type*} [DecidableEq F] (finger : F) (markerId : ι) (direction : Bool)
    (old fresh : Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : Neutral markerId newHeader) (dormantValid : Neutral markerId dormantHeader)
    (blocks : Fin 8 → ProjectionLocal.Projected β (Option (Datum α (HeadBoundary.Record ρ η (Option Bool)) ι)))
    (known : ∀ key, ObservedHeadBlueprint.bits old key = (blocks key).isSome)
    (initial final : Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (oldTree : OrderedContext.decorated blocks
      (ObservedHeadBlueprint.beforeContext (markerValue markerId) direction old oldHeader incomingHeader) = some initial)
    (newTree : OrderedContext.decorated blocks
      (ObservedHeadBlueprint.afterContext (markerValue markerId) direction fresh newHeader dormantHeader) = some final)
    (outside) (current : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (erases : current.mapRecords Prod.snd = ⟨initial,outside⟩)
    (config : MultiSourceProgram.Configuration F β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (positioned : MultiSourceSingleCursor.Represents finger current config)
    (valid : MultiSourceProgram.WellFormed config)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) config.tree) :
    ∃ target cursor reads cost,
      MultiSourceProgram.Run (MultiSourceSingleCursor.program (ImmutableSource.program LocalRecordActions.program) finger)
        (some (.ready (.ready (OrderedContext.Local.decoratedActions (ObservedHeadBlueprint.bits old)
          (ObservedHeadBlueprint.beforeContext (markerValue markerId) direction old oldHeader incomingHeader)
          (ObservedHeadBlueprint.afterContext (markerValue markerId) direction fresh newHeader dormantHeader))))) config
        (some (.ready (.ready []))) target reads cost ∧
      MultiSourceSingleCursor.Represents finger cursor target ∧ cursor.mapRecords Prod.snd = ⟨final,outside⟩ ∧
      target.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (Predicate markerId) target.tree ∧ MultiSourceProgram.WellFormed target ∧ cost ≤ 576 := by
  have actual := execute finger markerId blocks _ _
    (ObservedHeadBlueprint.block_order (markerValue markerId) direction old fresh oldHeader incomingHeader newHeader dormantHeader)
    (after_neutral markerId direction fresh newHeader dormantHeader newValid dormantValid)
    initial final oldTree newTree outside current erases config positioned valid aligned
  have bitsEq : ObservedHeadBlueprint.bits old = fun key => (blocks key).isSome := funext known
  rw [← bitsEq,ObservedHeadBlueprint.block_count] at actual
  exact actual

end ChaCha.Paper20261030.PacketAlignment
