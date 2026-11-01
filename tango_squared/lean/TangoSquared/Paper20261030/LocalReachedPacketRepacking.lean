import TangoSquared.Paper20261030.HeadPacketLayout
import TangoSquared.Paper20261030.PacketLayerAlignment

/-!
# Repacking the actual output of an immutable-id reassembly

The preceding reassembly determines erased packets, but deliberately does
not prescribe which physical vertex becomes each connector. This theorem
works directly with that erased output. It reads each reached immutable
id, derives residual-packet agreement from alignment, and reconstructs
the local layers. No assignment of future connector ids is an input.

`Repacked` states the resulting representation. Its leaf witnesses retain
the entire old block, including its internal immutable identifiers. Its
fork witnesses use the id actually read at that connector.
-/

namespace TangoSquared.Paper20261030.PacketLayers.Reached

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging RecordEditScript
open PacketAlignment

variable {κ α β ρ ι : Type*}

abbrev Cell (α ρ ι : Type*) := Context.Cell α ρ ι

def stagedTree (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (context : Source κ (Expression α ρ ι)) : Source β (Packet α ρ ι) :=
  PacketContext.all blocks (context.mapRecords (exposed markerId))

def Ordinary (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) : Source κ (Expression α ρ ι) → Prop
  | .leaf key expression => OrdinaryBase markerId (blocks key).rootRecord expression
  | .fork expression left right => OrdinaryBase markerId [] expression ∧ Ordinary markerId blocks left ∧ Ordinary markerId blocks right

inductive Repacked (blocks : κ → Source β (Packet α ρ ι)) :
    Source κ (Expression α ρ ι) → Source β (Cell α ρ ι) → Prop where
  | leaf (key : κ) (expression : Expression α ρ ι) (block : Source β (Cell α ρ ι))
      (erases : block.mapRecords Prod.snd = blocks key) :
      Repacked blocks (.leaf key expression)
        (block.setRoot (block.rootRecord.1,rebuilt block.rootRecord.1 (blocks key).rootRecord expression))
  | fork (expression : Expression α ρ ι) (left right : Source κ (Expression α ρ ι))
      (leftTree rightTree : Source β (Cell α ρ ι)) (id : ι)
      (leftReady : Repacked blocks left leftTree) (rightReady : Repacked blocks right rightTree) :
      Repacked blocks (.fork expression left right)
        (.fork (id,rebuilt id [] expression) leftTree rightTree)

private theorem root_set {σ : Type*} (tree : Source β σ) (record : σ) :
    (tree.setRoot record).rootRecord = record := by cases tree <;> rfl

private theorem set_set {σ : Type*} (tree : Source β σ) (first last : σ) :
    (tree.setRoot first).setRoot last = tree.setRoot last := by cases tree <;> rfl

private theorem set_root {σ : Type*} (tree : Source β σ) : tree.setRoot tree.rootRecord = tree := by
  cases tree <;> rfl

private theorem map_set {σ τ : Type*} (f : σ → τ) (tree : Source β σ) (record : σ) :
    (tree.setRoot record).mapRecords f = (tree.mapRecords f).setRoot (f record) := by cases tree <;> rfl

theorem repack (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (context : Source κ (Expression α ρ ι)) (ordinary : Ordinary markerId blocks context)
    (source : Source β (Cell α ρ ι))
    (erases : source.mapRecords Prod.snd = stagedTree markerId blocks context)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) source) :
    ∃ target,
      Transforms Context.repacking (Context.commands (context.mapRecords blueprint))
        source target (PhysicalPacketStaging.Context.budget context) ∧
      Repacked blocks context target ∧ target.mapRecords Prod.fst = source.mapRecords Prod.fst ∧
      SourceRecordPredicate.Holds (Predicate markerId) target := by
  induction context generalizing source with
  | leaf key expression =>
    have packetEq := congrArg Source.rootRecord erases
    simp only [Source.mapRecords_root,stagedTree,Source.mapRecords,PacketContext.all,root_set] at packetEq
    rw [← staged_exposed] at packetEq
    have atRoot := SourceRecordPredicate.root _ _ aligned
    change Aligned markerId source.rootRecord.1 source.rootRecord.2 at atRoot
    rw [packetEq] at atRoot
    have ready := PacketLayers.ready_from_alignment markerId source.rootRecord.1 _ expression ordinary atRoot
    let block := source.setRoot (source.rootRecord.1,(blocks key).rootRecord)
    have blockErases : block.mapRecords Prod.snd = blocks key := by
      simp only [block,map_set,erases,stagedTree,Source.mapRecords,PacketContext.all,set_set,set_root]
    let target := source.setRoot (source.rootRecord.1,rebuilt source.rootRecord.1 (blocks key).rootRecord expression)
    have actual := Transforms.edit (Context.repacking (α := α) (ρ := ρ) (ι := ι)) (blueprint expression) source
    have localEq : Context.repacking (blueprint expression) source.rootRecord = target.rootRecord := by
      simp only [Context.repacking,Context.atId,packetEq,repack_exact markerId _ _ _ ready,target,root_set]
    refine ⟨target,?_,?_,?_,?_⟩
    · simpa only [localEq,target,root_set,Context.commands,Source.mapRecords,PhysicalPacketStaging.Context.budget] using actual
    · have result := Repacked.leaf key expression block blockErases
      simpa only [block,root_set,set_set,target] using result
    · simp only [target,map_set,← Source.mapRecords_root Prod.fst source,set_root]
    · exact SourceRecordPredicate.setRoot _ _ _ aligned
        (rebuilt_aligned markerId source.rootRecord.1 _ expression atRoot)
  | fork expression left right ihl ihr =>
    cases source with
    | leaf => simp only [Source.mapRecords,stagedTree,PacketContext.all,reduceCtorEq] at erases
    | fork record leftTree rightTree =>
      simp only [Source.mapRecords,stagedTree,PacketContext.all,Source.fork.injEq] at erases
      obtain ⟨rootEq,leftEq,rightEq⟩ := erases
      obtain ⟨atRoot,leftAligned,rightAligned⟩ := (SourceRecordPredicate.fork _ _ _ _).mp aligned
      have ready : ReadyAt record.1 [] expression := by
        apply PacketLayers.ready_from_alignment markerId record.1 [] expression ordinary.1
        simpa only [staged_exposed,List.append_nil,Predicate,rootEq] using atRoot
      obtain ⟨leftTarget,leftRun,leftReady,leftIds,leftValid⟩ := ihl ordinary.2.1 leftTree leftEq leftAligned
      obtain ⟨rightTarget,rightRun,rightReady,rightIds,rightValid⟩ := ihr ordinary.2.2 rightTree rightEq rightAligned
      let fresh : Cell α ρ ι := (record.1,rebuilt record.1 [] expression)
      have first : Transforms Context.repacking [.edit (blueprint expression)]
          (.fork record leftTree rightTree) (.fork fresh leftTree rightTree) 2 := by
        have actual := Transforms.edit (Context.repacking (α := α) (ρ := ρ) (ι := ι)) (blueprint expression)
          (.fork record leftTree rightTree)
        have localEq : Context.repacking (blueprint expression) record = fresh := by
          simp only [Context.repacking,Context.atId,rootEq]
          have computed := repack_exact markerId record.1 [] expression ready
          simp only [staged_exposed,List.append_nil] at computed
          exact congrArg (fun packet => (record.1,packet)) computed
        simpa only [Source.rootRecord,Source.setRoot,localEq] using actual
      have actual := first.append ((leftRun.left fresh rightTree).append (rightRun.right fresh leftTarget))
      have cost : 2+((PhysicalPacketStaging.Context.budget left+2)+(PhysicalPacketStaging.Context.budget right+2)) =
          PhysicalPacketStaging.Context.budget (.fork expression left right) := by
        simp only [PhysicalPacketStaging.Context.budget]
        omega
      rw [cost] at actual
      refine ⟨.fork fresh leftTarget rightTarget,?_,Repacked.fork expression left right _ _ record.1 leftReady rightReady,?_,?_⟩
      · simpa only [Context.commands,Source.mapRecords,List.singleton_append] using actual
      · simp only [Source.mapRecords,leftIds,rightIds,fresh]
      · refine (SourceRecordPredicate.fork (Predicate markerId) fresh leftTarget rightTarget).mpr
          ⟨rebuilt_aligned markerId record.1 [] expression ?_,leftValid,rightValid⟩
        simpa only [staged_exposed,List.append_nil,Predicate,rootEq] using atRoot

end TangoSquared.Paper20261030.PacketLayers.Reached
