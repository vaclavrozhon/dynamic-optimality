import ChaCha.Paper20261030.EnclosedHeaderPath

set_option autoImplicit false

/-! A component's virtual bottom remains the same original-key leaf
when its root carries an enclosing packet. The path uses only the two
previously read wing bits. -/

namespace ChaCha.Paper20261030.ForestConnector.ThreeColors

open ColoredStorage SourcePointer SourcePositions

variable {α ρ τ : Type*}

theorem enclosed_header_leaf (forest : ProjectionForest.State (Option Bool) α ρ)
    (key : α) (record saved : List ρ) :
    ∃ data outside,
      locate ((configuration forest ⟨.leaf key record,[]⟩).tree.setRoot
        (saved++(configuration forest ⟨.leaf key record,[]⟩).tree.rootRecord)) (headerPath forest) =
        some ⟨.leaf key data,outside⟩ := by
  cases left : forest (some true) <;> cases right : forest (some false)
  all_goals
    simp [configuration,headerPath,left,right,MultiSourceProgram.join,single,Cursor.tree,plug,
      locate,descend,SourceLocalProgram.navigate,Source.setRoot,Source.rootRecord]

theorem reached_header_leaf (readPacket : τ → List ρ) (forest : ProjectionForest.State (Option Bool) α ρ)
    (key : α) (record saved : List ρ) (current : Cursor α τ)
    (view : current.focus.mapRecords readPacket = (configuration forest ⟨.leaf key record,[]⟩).tree.setRoot
      (saved++(configuration forest ⟨.leaf key record,[]⟩).tree.rootRecord)) :
    ∃ reached,
      descend current (headerPath forest) = some reached ∧ reached.focus = .leaf key reached.focus.rootRecord := by
  obtain ⟨data,outside,located⟩ := enclosed_header_leaf forest key record saved
  have erased : descend (current.mapRecords readPacket) (headerPath forest) =
      some ((⟨.leaf key data,outside⟩ : Cursor α (List ρ)).extend (current.ancestors.map (Frame.mapRecords readPacket))) := by
    change descend ⟨current.focus.mapRecords readPacket,current.ancestors.map (Frame.mapRecords readPacket)⟩ _ = _
    rw [view]
    exact descend_extend located _
  rw [descend_mapRecords] at erased
  cases found : descend current (headerPath forest) with
  | none => simp only [found,Option.map_none,reduceCtorEq] at erased
  | some reached =>
    simp only [found,Option.map_some,Option.some.injEq] at erased
    refine ⟨reached,rfl,?_⟩
    have focus := congrArg Cursor.focus erased
    cases shape : reached.focus with
    | leaf value stored =>
      have same : value = key := (show value = key ∧ readPacket stored = data from by
        simpa only [Cursor.mapRecords,Cursor.extend,shape,Source.mapRecords,Source.leaf.injEq] using focus).1
      simp only [same,Source.rootRecord]
    | fork stored left right =>
      simp only [Cursor.mapRecords,Cursor.extend,shape,Source.mapRecords,reduceCtorEq] at focus

end ChaCha.Paper20261030.ForestConnector.ThreeColors
