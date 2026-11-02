import ChaCha.Paper20261030.ThreeColorConfiguration
import ChaCha.Paper20261030.SourceFingerExtension
import ChaCha.Paper20261030.MultiSourceRecordMap

set_option autoImplicit false

/-! The header path computed from the two wing bits also works when the
component root carries an enclosing prefix. If both wings are absent,
the header is the root and that prefix is skipped by the subsequent read.
Otherwise the header lies below the root and its own packet is intact. -/

namespace ChaCha.Paper20261030.ForestConnector.ThreeColors

open ColoredStorage SourcePointer SourcePositions

variable {α ρ τ : Type*}

private theorem root_set (source : Source α ρ) (record : ρ) : (source.setRoot record).rootRecord = record := by
  cases source <;> rfl

theorem enclosed_header_atRoot (forest : ProjectionForest.State (Option Bool) α ρ)
    (header : Source α (List ρ)) (saved : List ρ) :
    ∃ focus outside,
      locate ((configuration forest ⟨header,[]⟩).tree.setRoot
        (saved++(configuration forest ⟨header,[]⟩).tree.rootRecord)) (headerPath forest) = some ⟨focus,outside⟩ ∧
      focus.rootRecord.drop (if (headerPath forest).isEmpty then saved.length else 0) = header.rootRecord := by
  cases left : forest (some true) <;> cases right : forest (some false)
  all_goals
    simp [configuration,headerPath,left,right,MultiSourceProgram.join,single,Cursor.tree,plug,
      locate,descend,SourceLocalProgram.navigate,Source.setRoot,Source.rootRecord,root_set,List.drop_left]
  all_goals cases header <;> simp [List.drop_left]

theorem reached_header (readPacket : τ → List ρ) (forest : ProjectionForest.State (Option Bool) α ρ)
    (header : Source α (List ρ)) (saved : List ρ) (current : Cursor α τ)
    (view : current.focus.mapRecords readPacket = (configuration forest ⟨header,[]⟩).tree.setRoot
      (saved++(configuration forest ⟨header,[]⟩).tree.rootRecord)) :
    ∃ reached,
      descend current (headerPath forest) = some reached ∧
      (readPacket reached.focus.rootRecord).drop (if (headerPath forest).isEmpty then saved.length else 0) = header.rootRecord := by
  obtain ⟨focus,outside,located,packet⟩ := enclosed_header_atRoot forest header saved
  have erased : descend (current.mapRecords readPacket) (headerPath forest) =
      some ((⟨focus,outside⟩ : Cursor α (List ρ)).extend (current.ancestors.map (Frame.mapRecords readPacket))) := by
    change descend ⟨current.focus.mapRecords readPacket,current.ancestors.map (Frame.mapRecords readPacket)⟩ _ = _
    rw [view]
    exact descend_extend located _
  rw [descend_mapRecords] at erased
  cases found : descend current (headerPath forest) with
  | none => simp only [found,Option.map_none,reduceCtorEq] at erased
  | some reached =>
    simp only [found,Option.map_some,Option.some.injEq] at erased
    have root := congrArg (fun cursor : Cursor α (List ρ) => cursor.focus.rootRecord) erased
    simp only [Cursor.mapRecords,Source.mapRecords_root,Cursor.extend] at root
    exact ⟨reached,rfl,by rw [root]; exact packet⟩

end ChaCha.Paper20261030.ForestConnector.ThreeColors
