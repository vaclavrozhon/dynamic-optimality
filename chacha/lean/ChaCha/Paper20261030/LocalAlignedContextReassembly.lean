import ChaCha.Paper20261030.ImmutablePacketAlignment
import ChaCha.Paper20261030.LocalDecoratedReassembly

/-! The finite-context reassembly controller with physical-id alignment
maintained throughout. Installed prefixes contain only temporary markers,
virtual headers, and delimiters. Rotations preserve complete vertex
records; writes retain the reached immutable id. The theorem includes
arbitrary opaque blocks and an arbitrary untouched outer context.
-/

namespace ChaCha.Paper20261030.PacketAlignment

open ColoredStorage SourcePointer SourceLocalProgram RouterProjection ProjectionLocal
open OrderedContext LocalProjectedRotation PhysicalPacketStaging
open LocalRecordActions (Action)

variable {κ α β ρ ι : Type*}

theorem safe_nil (markerId : ι) : SafeActions (α := α) (ρ := ρ) markerId [] := by
  intro action member
  cases member

theorem safe_append (markerId : ι) (first last : List (Action (Option (Datum α ρ ι))))
    (hf : SafeActions markerId first) (hl : SafeActions markerId last) : SafeActions markerId (first++last) := by
  intro action member
  exact (List.mem_append.mp member).elim (hf action) (hl action)

theorem safe_nav (markerId : ι) (move : DynamicOptimality.LocalProgram.Move) :
    SafeActions (α := α) (ρ := ρ) markerId [.nav move] := by
  intro action member
  cases List.mem_singleton.mp member
  trivial

theorem safe_drop (markerId : ι) (count : Nat) : SafeActions (α := α) (ρ := ρ) markerId [.drop count] := by
  intro action member
  cases List.mem_singleton.mp member
  trivial

theorem safe_prepend (markerId : ι) (records : Packet α ρ ι) (neutral : Neutral markerId records) :
    SafeActions markerId [.prepend records] := by
  intro action member
  cases List.mem_singleton.mp member
  exact neutral

theorem safe_left (markerId : ι) (actions : List (Action (Option (Datum α ρ ι)))) (safe : SafeActions markerId actions) :
    SafeActions markerId (LocalRecordActions.left actions) :=
  safe_append markerId [.nav .left] _ (safe_nav markerId .left)
    (safe_append markerId actions [.nav .up] safe (safe_nav markerId .up))

theorem safe_right (markerId : ι) (actions : List (Action (Option (Datum α ρ ι)))) (safe : SafeActions markerId actions) :
    SafeActions markerId (LocalRecordActions.right actions) :=
  safe_append markerId [.nav .right] _ (safe_nav markerId .right)
    (safe_append markerId actions [.nav .up] safe (safe_nav markerId .up))

theorem safe_liftLeft (markerId : ι) (a b : Bool) (actions : List (Action (Option (Datum α ρ ι))))
    (safe : SafeActions markerId actions) : SafeActions markerId (liftLeft a b actions) := by
  cases a <;> cases b <;> simp only [liftLeft,Bool.false_eq_true,if_false,if_true]
  all_goals first | exact safe_nil markerId | exact safe | exact safe_left markerId actions safe

theorem safe_liftRight (markerId : ι) (a b : Bool) (actions : List (Action (Option (Datum α ρ ι))))
    (safe : SafeActions markerId actions) : SafeActions markerId (liftRight a b actions) := by
  cases a <;> cases b <;> simp only [liftRight,Bool.false_eq_true,if_false,if_true]
  all_goals first | exact safe_nil markerId | exact safe | exact safe_right markerId actions safe

theorem safe_route (markerId : ι) (a b c : Bool) : SafeActions (α := α) (ρ := ρ) markerId (route a b c) := by
  unfold route
  split <;> first | exact safe_nav markerId _ | exact safe_nil markerId

theorem safe_routeLeft (markerId : ι) (a b c : Bool) : SafeActions (α := α) (ρ := ρ) markerId (routeLeft a b c) := by
  unfold routeLeft
  split <;> first | exact safe_nav markerId _ | exact safe_nil markerId

theorem normalize_safe (markerId : ι) (bits : κ → Bool) (shape : Router κ) :
    SafeActions (α := α) (ρ := ρ) markerId (OrderedContext.Local.normalize bits shape) := by
  cases shape with
  | empty | leaf => simpa only [OrderedContext.Local.normalize] using (safe_nil (α := α) (ρ := ρ) markerId)
  | fork left right => cases left with
    | empty => simpa only [OrderedContext.Local.normalize] using (safe_nil (α := α) (ρ := ρ) markerId)
    | leaf key =>
      rw [OrderedContext.Local.normalize]
      exact safe_liftRight markerId _ _ _ (normalize_safe markerId bits right)
    | fork u v =>
      rw [OrderedContext.Local.normalize]
      exact safe_append markerId _ _ (safe_route markerId _ _ _)
        (normalize_safe markerId bits (.fork u (.fork v right)))
termination_by weight shape
decreasing_by all_goals simp only [weight,Router.internalCount]; omega

theorem restore_safe (markerId : ι) (bits : κ → Bool) (shape : Router κ) :
    SafeActions (α := α) (ρ := ρ) markerId (OrderedContext.Local.restore bits shape) := by
  cases shape with
  | empty | leaf => simpa only [OrderedContext.Local.restore] using (safe_nil (α := α) (ρ := ρ) markerId)
  | fork left right => cases left with
    | empty => simpa only [OrderedContext.Local.restore] using (safe_nil (α := α) (ρ := ρ) markerId)
    | leaf key =>
      rw [OrderedContext.Local.restore]
      exact safe_liftRight markerId _ _ _ (restore_safe markerId bits right)
    | fork u v =>
      rw [OrderedContext.Local.restore]
      exact safe_append markerId _ _
        (restore_safe markerId bits (.fork u (.fork v right))) (safe_routeLeft markerId _ _ _)
termination_by weight shape
decreasing_by all_goals simp only [weight,Router.internalCount]; omega

theorem clear_safe (markerId : ι) (bits : κ → Bool) (context : Source κ (Packet α ρ ι)) :
    SafeActions markerId (OrderedContext.Local.clear bits context) := by
  induction context with
  | leaf key records => exact safe_drop markerId records.length
  | fork records left right ihl ihr =>
    exact safe_append markerId _ _
      (safe_append markerId _ _ (safe_drop markerId records.length) (safe_liftLeft markerId _ _ _ ihl))
      (safe_liftRight markerId _ _ _ ihr)

theorem install_safe (markerId : ι) (bits : κ → Bool) (context : Source κ (Packet α ρ ι))
    (neutral : SourceRecordPredicate.Holds (Neutral markerId) context) :
    SafeActions markerId (OrderedContext.Local.install bits context) := by
  induction context with
  | leaf key records => exact safe_prepend markerId records ((SourceRecordPredicate.leaf _ _ _).mp neutral)
  | fork records left right ihl ihr =>
    obtain ⟨atRoot,leftValid,rightValid⟩ := (SourceRecordPredicate.fork _ _ _ _).mp neutral
    exact safe_append markerId _ _
      (safe_append markerId _ _ (safe_liftLeft markerId _ _ _ (ihl leftValid)) (safe_liftRight markerId _ _ _ (ihr rightValid)))
      (safe_prepend markerId records atRoot)

theorem decorated_safe (markerId : ι) (bits : κ → Bool) (before after : Source κ (Packet α ρ ι))
    (neutral : SourceRecordPredicate.Holds (Neutral markerId) after) :
    SafeActions markerId (OrderedContext.Local.decoratedActions bits before after) :=
  safe_append markerId _ _
    (safe_append markerId _ _ (clear_safe markerId bits before)
      (safe_append markerId _ _ (normalize_safe markerId bits before.shape) (restore_safe markerId bits after.shape)))
    (install_safe markerId bits after neutral)

theorem reassemble (markerId : ι) (blocks : κ → Projected β (Option (Datum α ρ ι)))
    (before after : Source κ (Packet α ρ ι)) (ordered : before.shape.leaves = after.shape.leaves)
    (neutral : SourceRecordPredicate.Holds (Neutral markerId) after)
    (initial final : Source β (Packet α ρ ι))
    (oldTree : decorated blocks before = some initial) (newTree : decorated blocks after = some final)
    (outside : List (Frame β (Packet α ρ ι))) (current : Cursor β (ι × Packet α ρ ι))
    (erases : current.mapRecords Prod.snd = ⟨initial,outside⟩)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) current.tree) :
    ∃ target reads cost,
      Run (ImmutableSource.program LocalRecordActions.program)
        (.ready (.ready (OrderedContext.Local.decoratedActions (fun key => (blocks key).isSome) before after))) current
        (.ready (.ready [])) target reads cost ∧
      target.mapRecords Prod.snd = ⟨final,outside⟩ ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (Predicate markerId) target.tree ∧ cost ≤ 72*before.shape.leaves.length := by
  have plain := OrderedContext.Local.decorated_run blocks before after ordered
  rw [oldTree,newTree] at plain
  obtain ⟨plainReads,plainCost,plainRun,bound⟩ := plain outside
  obtain ⟨target,reads,cost,actual,targetErases,bounded⟩ :=
    ImmutableSource.compile_run LocalRecordActions.program plainRun current erases
  have targetAligned := PacketAlignment.run markerId (decorated_safe markerId _ before after neutral) actual aligned
  have inventory := (ImmutableSource.run_invariant actual trivial).2
  exact ⟨target,reads,cost,actual,targetErases,inventory.symm,targetAligned,by omega⟩

theorem execute {F : Type*} [DecidableEq F] (finger : F)
    (markerId : ι) (blocks : κ → Projected β (Option (Datum α ρ ι)))
    (before after : Source κ (Packet α ρ ι)) (ordered : before.shape.leaves = after.shape.leaves)
    (neutral : SourceRecordPredicate.Holds (Neutral markerId) after)
    (initial final : Source β (Packet α ρ ι))
    (oldTree : decorated blocks before = some initial) (newTree : decorated blocks after = some final)
    (outside : List (Frame β (Packet α ρ ι))) (current : Cursor β (ι × Packet α ρ ι))
    (erases : current.mapRecords Prod.snd = ⟨initial,outside⟩)
    (config : MultiSourceProgram.Configuration F β (ι × Packet α ρ ι))
    (positioned : MultiSourceSingleCursor.Represents finger current config)
    (valid : MultiSourceProgram.WellFormed config)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) config.tree) :
    ∃ target cursor reads cost,
      MultiSourceProgram.Run (MultiSourceSingleCursor.program (ImmutableSource.program LocalRecordActions.program) finger)
        (some (.ready (.ready (OrderedContext.Local.decoratedActions (fun key => (blocks key).isSome) before after)))) config
        (some (.ready (.ready []))) target reads cost ∧
      MultiSourceSingleCursor.Represents finger cursor target ∧ cursor.mapRecords Prod.snd = ⟨final,outside⟩ ∧
      target.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (Predicate markerId) target.tree ∧ MultiSourceProgram.WellFormed target ∧
      cost ≤ 72*before.shape.leaves.length := by
  have currentAligned : SourceRecordPredicate.Holds (Predicate markerId) current.tree := by
    rw [← positioned.1]
    exact aligned
  obtain ⟨cursor,sourceReads,cost,sourceRun,targetErases,inventory,targetAligned,bound⟩ :=
    reassemble markerId blocks before after ordered neutral initial final oldTree newTree outside current erases currentAligned
  obtain ⟨target,actual,targetRep⟩ := MultiSourceSingleCursor.compile_run _ finger sourceRun config positioned
  refine ⟨target,cursor,_,cost,actual,targetRep,targetErases,?_,?_,actual.wellFormed valid,bound⟩
  · rw [targetRep.1,inventory,← positioned.1]
  · rw [targetRep.1]
    exact targetAligned

end ChaCha.Paper20261030.PacketAlignment
