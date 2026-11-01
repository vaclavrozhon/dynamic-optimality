import LabelTimeline

/-!
Batch administration is a concrete label timeline. A finite set of paid
ports permits arbitrary bounded new labels; all other record labels must
weakly decrease. Each paid port supplies at most one paid timeline slot.
-/
namespace GreedyForest.Timeline

variable {Record Block : Type*} [DecidableEq Record]

def relabelUpdate (target : Record → ℤ) (ports : Finset Record) (v : Record) :
    Update Record Block where
  record := v
  value := target v
  origin := if v ∈ ports then .paid else .free
  good := false

def relabel (target : Record → ℤ) (ports : Finset Record) (records : List Record) :
    List (Update Record Block) := records.map (relabelUpdate target ports)

/-- A whole administrative relabeling is valid from a pointwise
nonincrease certificate outside paid ports, without any sum bound. -/
theorem valid_relabel {K : ℤ} (labels target : Record → ℤ)
    (ports : Finset Record) (records : List Record)
    (hb : ∀ v ∈ records, 1 ≤ target v ∧ target v ≤ K)
    (hfree : ∀ v, v ∉ ports → target v ≤ labels v) :
    Valid K labels (relabel (Block:=Block) target ports records) := by
  induction records generalizing labels with
  | nil => trivial
  | cons v rest ih =>
      refine ⟨⟨hb v (by simp),?_,?_⟩,?_⟩
      · intro htag
        by_cases hv : v ∈ ports
        · simp [relabelUpdate,hv] at htag
        · exact hfree v hv
      · simp [relabelUpdate]
      · apply ih (applyUpdate labels (relabelUpdate target ports v))
          (fun w hw => hb w (by simp [hw]))
        intro w hw
        by_cases heq : w=v
        · subst w; simp [applyUpdate,relabelUpdate]
        · simpa [applyUpdate,relabelUpdate,heq] using hfree w hw

theorem run_relabel_preserves_target (labels target : Record → ℤ)
    (ports : Finset Record) (records : List Record) (v : Record) (hv : labels v=target v) :
    run labels (relabel (Block:=Block) target ports records) v = target v := by
  induction records generalizing labels with
  | nil => exact hv
  | cons w rest ih =>
      apply ih (applyUpdate labels (relabelUpdate target ports w))
      by_cases heq : v=w
      · subst v; simp [applyUpdate,relabelUpdate]
      · simpa [applyUpdate,relabelUpdate,heq] using hv

theorem run_relabel_at_mem (labels target : Record → ℤ)
    (ports : Finset Record) (records : List Record) (v : Record) (hv : v ∈ records) :
    run labels (relabel (Block:=Block) target ports records) v = target v := by
  induction records generalizing labels with
  | nil => simp at hv
  | cons w rest ih =>
      rcases List.mem_cons.mp hv with heq | hrest
      · subst v
        change run (applyUpdate labels (relabelUpdate target ports w))
          (relabel (Block:=Block) target ports rest) w = target w
        apply run_relabel_preserves_target
        simp [applyUpdate,relabelUpdate]
      · exact ih (applyUpdate labels (relabelUpdate target ports w)) hrest

omit [DecidableEq Record] in
theorem update_record_injective (updates : List (Update Record Block))
    (hn : (updates.map Update.record).Nodup) :
    Function.Injective (fun t : Fin updates.length => (updates.get t).record) := by
  have hu := hn.of_map
  have hrec := List.inj_on_of_nodup_map hn
  intro a b hab
  apply hu.injective_get
  exact hrec (List.get_mem updates a) (List.get_mem updates b) hab

/-- The paid parameter counts actual paid ports, even if a batch also
updates arbitrarily many other labels for free. -/
theorem paid_relabel_card_le_ports (target : Record → ℤ) (ports : Finset Record)
    (records : List Record) (hn : records.Nodup) :
    Nat.card (Paid (relabel (Block:=Block) target ports records)) ≤ ports.card := by
  classical
  let updates := relabel (Block:=Block) target ports records
  have hrecords : (updates.map Update.record).Nodup := by
    simpa [updates,relabel,relabelUpdate,List.map_map,Function.comp_def] using hn
  have hinj := update_record_injective updates hrecords
  have hport : ∀ u ∈ updates, u.origin = .paid → u.record ∈ ports := by
    intro u hu htag
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
    by_contra hnot
    change v ∉ ports at hnot
    simp [relabelUpdate,hnot] at htag
  let project : Paid updates → {v // v ∈ ports} := fun p =>
    ⟨(updates.get p.val).record,hport _ (List.get_mem updates p.val) p.property⟩
  have hproject : Function.Injective project := by
    intro a b hab
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hab)
  have hc := Nat.card_le_card_of_injective project hproject
  simpa using hc

end GreedyForest.Timeline

#print axioms GreedyForest.Timeline.valid_relabel
#print axioms GreedyForest.Timeline.paid_relabel_card_le_ports
