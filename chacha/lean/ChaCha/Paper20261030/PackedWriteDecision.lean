import ChaCha.Paper20261030.PackedIdentifierUniqueness

/-! Computing a packed write from the list actually read at the current
physical finger. Unique immutable identifiers ensure that exactly the
intended slot changes, even when suppressed ancestors precede that slot.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer ProjectionLocal

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C] [Fintype C]

def updateEntries (identifier : ρ → ι) (wanted : ι) (fresh : ρ) (records : List ρ) : List ρ :=
  records.map (fun record => if identifier record = wanted then fresh else record)

omit [LinearOrder C] [Fintype C] in
theorem updateEntries_absent (identifier : ρ → ι) (wanted : ι) (fresh : ρ) (records : List ρ)
    (absent : wanted ∉ records.map identifier) : updateEntries identifier wanted fresh records = records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
    have different : identifier record ≠ wanted := by
      intro same
      apply absent
      simp only [List.map_cons,List.mem_cons,same,true_or]
    have tailAbsent : wanted ∉ rest.map identifier := fun member => absent (List.mem_cons_of_mem _ member)
    simp only [updateEntries,List.map_cons,if_neg different] at ih ⊢
    rw [ih tailAbsent]

omit [LinearOrder C] [Fintype C] in
theorem updateEntries_unique (identifier : ρ → ι) (old fresh : ρ) (extras tail : List ρ)
    (unique : ((extras ++ old::tail).map identifier).Nodup) :
    updateEntries identifier (identifier old) fresh (extras ++ old::tail) = extras ++ fresh::tail := by
  induction extras with
  | nil =>
    simp only [List.nil_append,List.map_cons,List.nodup_cons] at unique ⊢
    change (if identifier old = identifier old then fresh else old) :: updateEntries identifier (identifier old) fresh tail = _
    rw [if_pos rfl,updateEntries_absent identifier (identifier old) fresh tail unique.1]
  | cons record rest ih =>
    simp only [List.cons_append,List.map_cons,List.nodup_cons] at unique
    have different : identifier record ≠ identifier old := by
      intro same
      apply unique.1
      simp only [List.map_append,List.map_cons,List.mem_append,List.mem_cons,same,true_or,or_true]
    change (if identifier record = identifier old then fresh else record) ::
      updateEntries identifier (identifier old) fresh (rest ++ old::tail) = record :: (rest ++ fresh::tail)
    rw [if_neg different,ih unique.2]

theorem write_record_exact [DecidableEq α] (identifier : ρ → ι) (color : α → C) (source : Cursor α ρ)
    (fresh : ρ) (unique : (source.tree.inventory identifier).Nodup) {physical : Cursor α (List ρ)}
    (represented : Represents color (source.focus.rootOwner color) source physical) :
    Represents color (source.focus.rootOwner color) ⟨source.focus.setRoot fresh,source.ancestors⟩
      ⟨physical.focus.setRoot (updateEntries identifier (identifier source.focus.rootRecord) fresh physical.focus.rootRecord),
        physical.ancestors⟩ := by
  obtain ⟨a,ha⟩ := packed_exists color _ source.focus (Source.rootOwner_mem color _)
  let b := a.setRoot (a.rootRecord.modifyHead (fun _ => fresh))
  have hb : packed color (source.focus.rootOwner color) (source.focus.setRoot fresh) = some b := by
    simp only [packed_setRoot,if_true,ha,Option.map_some,b]
  obtain ⟨extras,rest,hbefore,hafter,hframes⟩ := packed_cursor_context color _
    (Source.support_setRoot color source.focus fresh).symm ha hb source.ancestors
  have contextRep := represents_of_context color _ source.focus source.ancestors ha extras rest hbefore hframes
  have equal := Represents.unique color _ source represented contextRep
  have localUnique := represented_root_unique identifier color _ source physical represented unique
  rw [equal] at localUnique ⊢
  obtain ⟨tail,head⟩ := packed_root_head color source.focus ha
  have rootList : (prepend extras a).rootRecord = extras ++ source.focus.rootRecord::tail := by
    cases a <;> simpa only [prepend,Source.setRoot,Source.rootRecord] using congrArg (extras ++ ·) head
  rw [rootList] at localUnique ⊢
  have updated := updateEntries_unique identifier source.focus.rootRecord fresh extras tail localUnique
  rw [updated]
  have target : (prepend extras a).setRoot (extras ++ fresh::tail) = prepend extras b := by
    cases a <;> simp_all only [b,prepend,Source.setRoot,Source.rootRecord,List.modifyHead_cons]
  rw [target]
  exact represents_of_context color _ _ _ hb extras rest hafter hframes

end ChaCha.Paper20261030.ColoredStorage
