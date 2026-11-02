import ChaCha.Paper20261030.Restriction
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Multiset.AddSub

/-!
# Storing source records in color restrictions

A source vertex has a record, and each leaf has a color. Every source
record is assigned to one color. At a branch that survives in some color
restriction, we choose such a color; otherwise we choose any color below
the branch. The record is stored at the root of that restriction.

This construction concerns storage and routing. Charged navigation to the
stored records is a separate simulation obligation.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open RouterProjection

variable {α ρ C : Type*}

inductive Source (α ρ : Type*) where
  | leaf (key : α) (record : ρ)
  | fork (record : ρ) (left right : Source α ρ)

def Source.shape : Source α ρ → Router α
  | .leaf key _ => .leaf key
  | .fork _ l r => .fork l.shape r.shape

def Source.records : Source α ρ → Multiset ρ
  | .leaf _ record => {record}
  | .fork record l r => {record} + l.records + r.records

def Source.rootRecord : Source α ρ → ρ
  | .leaf _ record | .fork record _ _ => record

def Source.support [DecidableEq C] (color : α → C) : Source α ρ → Finset C
  | .leaf key _ => {color key}
  | .fork _ l r => l.support color ∪ r.support color

theorem Source.support_nonempty [DecidableEq C] (color : α → C) (t : Source α ρ) :
    (t.support color).Nonempty := by
  induction t with
  | leaf key record => exact ⟨color key,by simp [support]⟩
  | fork record l r ihl ihr =>
    obtain ⟨q,hq⟩ := ihl
    exact ⟨q,by simp [support,hq]⟩

inductive Stored (α ρ : Type*) where
  | empty
  | leaf (key : α) (records : List ρ)
  | fork (records : List ρ) (left right : Stored α ρ)

def Stored.shape : Stored α ρ → Router α
  | .empty => .empty
  | .leaf key _ => .leaf key
  | .fork _ l r => .fork l.shape r.shape

def Stored.rootRecords : Stored α ρ → List ρ
  | .empty => []
  | .leaf _ records | .fork records _ _ => records

def Stored.records : Stored α ρ → Multiset ρ
  | .empty => 0
  | .leaf _ records => records
  | .fork records l r => (records : Multiset ρ) + l.records + r.records

def Stored.join : Stored α ρ → Stored α ρ → Stored α ρ
  | .empty,r => r
  | l,.empty => l
  | l,r => .fork [] l r

def Stored.addRoot (record : ρ) : Stored α ρ → Stored α ρ
  | .empty => .empty
  | .leaf key records => .leaf key (record :: records)
  | .fork records l r => .fork (record :: records) l r

theorem Stored.shape_join (l r : Stored α ρ) :
    (l.join r).shape = l.shape.join r.shape := by
  cases l <;> cases r <;> rfl

theorem Stored.shape_addRoot (record : ρ) (t : Stored α ρ) :
    (t.addRoot record).shape = t.shape := by cases t <;> rfl

theorem Stored.records_join (l r : Stored α ρ) :
    (l.join r).records = l.records + r.records := by
  cases l <;> cases r <;> simp [join,records]

theorem Stored.records_addRoot (record : ρ) {t : Stored α ρ} (ht : t ≠ .empty) :
    (t.addRoot record).records = {record} + t.records := by
  cases t <;> simp_all [addRoot,records,add_assoc,← Multiset.cons_coe,Multiset.cons_add]

theorem Stored.shape_eq_empty (t : Stored α ρ) : t.shape = .empty ↔ t = .empty := by
  cases t <;> simp [shape]

def owner [LinearOrder C] (color : α → C) (l r : Source α ρ) : C :=
  if h : (l.support color ∩ r.support color).Nonempty then
    (l.support color ∩ r.support color).min' h
  else
    (l.support color ∪ r.support color).min'
      (Finset.Nonempty.mono Finset.subset_union_left (l.support_nonempty color))

theorem owner_mem [LinearOrder C] (color : α → C) (l r : Source α ρ) :
    owner color l r ∈ l.support color ∪ r.support color := by
  unfold owner
  split
  · exact Finset.mem_union_left _ (Finset.mem_inter.mp (Finset.min'_mem _ _)).1
  · exact Finset.min'_mem _ _

theorem owner_shared [LinearOrder C] (color : α → C) (l r : Source α ρ)
    (h : (l.support color ∩ r.support color).Nonempty) :
    owner color l r ∈ l.support color ∧ owner color l r ∈ r.support color := by
  unfold owner
  rw [dif_pos h]
  exact Finset.mem_inter.mp (Finset.min'_mem _ _)

def pack [LinearOrder C] (color : α → C) (q : C) : Source α ρ → Stored α ρ
  | .leaf key record => if color key = q then .leaf key [record] else .empty
  | .fork record l r =>
    let joined := (pack color q l).join (pack color q r)
    if owner color l r = q then joined.addRoot record else joined

theorem pack_shape [LinearOrder C] (color : α → C) (q : C) (t : Source α ρ) :
    (pack color q t).shape = t.shape.prune (fun key => decide (color key = q)) := by
  induction t with
  | leaf key record => by_cases h : color key = q <;> simp [pack,h,Source.shape,Stored.shape,Router.prune]
  | fork record l r ihl ihr =>
    simp only [pack,Source.shape,Router.prune]
    split <;> simp only [Stored.shape_addRoot,Stored.shape_join,ihl,ihr]

theorem pack_nonempty [LinearOrder C] (color : α → C) (q : C) (t : Source α ρ) :
    pack color q t ≠ .empty ↔ q ∈ t.support color := by
  induction t with
  | leaf key record => by_cases h : color key = q <;> simp_all [pack,Source.support,eq_comm]
  | fork record l r ihl ihr =>
    have hj : (pack color q l).join (pack color q r) ≠ .empty ↔
        pack color q l ≠ .empty ∨ pack color q r ≠ .empty := by
      cases pack color q l <;> cases pack color q r <;> simp [Stored.join]
    have ha : ∀ t : Stored α ρ, t.addRoot record ≠ .empty ↔ t ≠ .empty := by
      intro t
      cases t <;> simp [Stored.addRoot]
    simp only [pack,Source.support,Finset.mem_union]
    split <;> simp only [ha,hj,ihl,ihr]

theorem pack_fork_records [LinearOrder C] (color : α → C) (q : C) (record : ρ)
    (l r : Source α ρ) :
    (pack color q (.fork record l r)).records =
      (pack color q l).records + (pack color q r).records +
        if owner color l r = q then {record} else 0 := by
  by_cases ho : owner color l r = q
  · have hn : pack color q (.fork record l r) ≠ .empty :=
      (pack_nonempty color q _).mpr (ho ▸ owner_mem color l r)
    have hj : (pack color q l).join (pack color q r) ≠ .empty := by
      intro he
      apply hn
      simp only [pack,if_pos ho,he,Stored.addRoot]
    simp only [pack,if_pos ho,Stored.records_addRoot record hj,Stored.records_join]
    ac_rfl
  · simp only [pack,if_neg ho,Stored.records_join,add_zero]

theorem pack_records_sum [LinearOrder C] [Fintype C] (color : α → C) (t : Source α ρ) :
    ∑ q : C, (pack color q t).records = t.records := by
  induction t with
  | leaf key record => simp [pack,apply_ite,Stored.records,Source.records,eq_comm]
  | fork record l r ihl ihr =>
    simp only [pack_fork_records,Finset.sum_add_distrib,ihl,ihr,Source.records]
    simp [eq_comm,add_assoc,add_comm,add_left_comm]

def Stored.Bounded (capacity : Nat) : Stored α ρ → Prop
  | .empty => True
  | .leaf _ records => records.length ≤ capacity
  | .fork records l r => records.length ≤ capacity ∧ l.Bounded capacity ∧ r.Bounded capacity

theorem Stored.Bounded.mono {a b : Nat} {t : Stored α ρ} (h : t.Bounded a) (hab : a ≤ b) :
    t.Bounded b := by
  induction t with
  | empty => trivial
  | leaf key records => exact h.trans hab
  | fork records l r ihl ihr => exact ⟨h.1.trans hab,ihl h.2.1,ihr h.2.2⟩

theorem Stored.Bounded.root {capacity : Nat} {t : Stored α ρ} (h : t.Bounded capacity) :
    t.rootRecords.length ≤ capacity := by
  cases t with
  | empty => exact Nat.zero_le _
  | leaf => exact h
  | fork => exact h.1

theorem Stored.bounded_join {capacity : Nat} {l r : Stored α ρ}
    (hl : l.Bounded capacity) (hr : r.Bounded capacity) : (l.join r).Bounded capacity := by
  cases l <;> cases r <;> simp_all [Bounded,join]

theorem Stored.bounded_addRoot {capacity : Nat} (record : ρ) {t : Stored α ρ}
    (ht : t.Bounded capacity) (hroot : (t.addRoot record).rootRecords.length ≤ capacity) :
    (t.addRoot record).Bounded capacity := by
  cases t <;> simp_all [Bounded,addRoot,rootRecords]

theorem Stored.join_root_bound {capacity : Nat} {l r : Stored α ρ}
    (hl : l.rootRecords.length ≤ capacity) (hr : r.rootRecords.length ≤ capacity) :
    (l.join r).rootRecords.length ≤ capacity := by
  cases l <;> cases r <;> simp_all [join,rootRecords]

theorem Stored.join_root_both {l r : Stored α ρ} (hl : l ≠ .empty) (hr : r ≠ .empty) :
    (l.join r).rootRecords = [] := by
  cases l <;> cases r <;> simp_all [join,rootRecords]

theorem Stored.addRoot_length (record : ρ) {t : Stored α ρ} (ht : t ≠ .empty) :
    (t.addRoot record).rootRecords.length = t.rootRecords.length + 1 := by
  cases t <;> simp_all [addRoot,rootRecords]

theorem Stored.join_empty_right (t : Stored α ρ) : t.join .empty = t := by
  cases t <;> rfl

theorem owner_missing_disjoint [LinearOrder C] (color : α → C) (q : C) (l r : Source α ρ)
    (ho : owner color l r = q) (hmissing : q ∉ l.support color ∨ q ∉ r.support color) :
    l.support color ∩ r.support color = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hn
  have hs := ho ▸ owner_shared color l r hn
  rcases hmissing with h | h
  · exact h hs.1
  · exact h hs.2

theorem pack_root_bound [LinearOrder C] (color : α → C) (q : C) (t : Source α ρ) :
    (pack color q t).rootRecords.length ≤ (t.support color).card := by
  induction t with
  | leaf key record => by_cases h : color key = q <;> simp [pack,h,Stored.rootRecords,Source.support]
  | fork record l r ihl ihr =>
    have hcl : (l.support color).card ≤ (l.support color ∪ r.support color).card :=
      Finset.card_le_card Finset.subset_union_left
    have hcr : (r.support color).card ≤ (l.support color ∪ r.support color).card :=
      Finset.card_le_card Finset.subset_union_right
    by_cases ho : owner color l r = q
    · have hn : pack color q (.fork record l r) ≠ .empty :=
        (pack_nonempty color q _).mpr (ho ▸ owner_mem color l r)
      have hj : (pack color q l).join (pack color q r) ≠ .empty := by
        intro he
        apply hn
        simp only [pack,if_pos ho,he,Stored.addRoot]
      simp only [pack,if_pos ho,Stored.addRoot_length record hj,Source.support]
      by_cases hl : pack color q l = .empty
      · rw [hl,Stored.join]
        have hmissing : q ∉ l.support color := by
          intro hq
          exact (pack_nonempty color q l).mpr hq hl
        have he := owner_missing_disjoint color q l r ho (Or.inl hmissing)
        have hcard := Finset.card_union_add_card_inter (l.support color) (r.support color)
        have hpos := Finset.card_pos.mpr (l.support_nonempty color)
        simp only [he,Finset.card_empty,Nat.add_zero] at hcard
        omega
      · by_cases hr : pack color q r = .empty
        · rw [hr,Stored.join_empty_right]
          have hmissing : q ∉ r.support color := by
            intro hq
            exact (pack_nonempty color q r).mpr hq hr
          have he := owner_missing_disjoint color q l r ho (Or.inr hmissing)
          have hcard := Finset.card_union_add_card_inter (l.support color) (r.support color)
          have hpos := Finset.card_pos.mpr (r.support_nonempty color)
          simp only [he,Finset.card_empty,Nat.add_zero] at hcard
          omega
        · rw [Stored.join_root_both hl hr]
          have hp := Finset.card_pos.mpr
            (show (l.support color ∪ r.support color).Nonempty from
              ⟨owner color l r,owner_mem color l r⟩)
          simpa using hp
    · simp only [pack,if_neg ho,Source.support]
      exact Stored.join_root_bound (ihl.trans hcl) (ihr.trans hcr)

theorem pack_bounded [LinearOrder C] (color : α → C) (q : C) (t : Source α ρ) :
    (pack color q t).Bounded (t.support color).card := by
  induction t with
  | leaf key record => by_cases h : color key = q <;> simp [pack,h,Stored.Bounded,Source.support]
  | fork record l r ihl ihr =>
    have hcl : (l.support color).card ≤ (l.support color ∪ r.support color).card :=
      Finset.card_le_card Finset.subset_union_left
    have hcr : (r.support color).card ≤ (l.support color ∪ r.support color).card :=
      Finset.card_le_card Finset.subset_union_right
    have hj := Stored.bounded_join (ihl.mono hcl) (ihr.mono hcr)
    have hroot := pack_root_bound color q (.fork record l r)
    simp only [pack,Source.support] at hroot ⊢
    by_cases ho : owner color l r = q
    · simp only [if_pos ho] at hroot ⊢
      exact Stored.bounded_addRoot record hj hroot
    · simp only [if_neg ho]
      exact hj

/-- All records are stored at the projected routing vertices, with at most
one slot per available color at any vertex. -/
theorem pack_bounded_colors [LinearOrder C] [Fintype C] (color : α → C) (q : C)
    (t : Source α ρ) : (pack color q t).Bounded (Fintype.card C) :=
  (pack_bounded color q t).mono (Finset.card_le_univ _)

theorem current_record_at_root [LinearOrder C] (color : α → C) (t : Source α ρ) :
    ∃ q, t.rootRecord ∈ (pack color q t).rootRecords := by
  cases t with
  | leaf key record => exact ⟨color key,by simp [Source.rootRecord,pack,Stored.rootRecords]⟩
  | fork record l r =>
    refine ⟨owner color l r,?_⟩
    have hn : pack color (owner color l r) (.fork record l r) ≠ .empty :=
      (pack_nonempty color _ _).mpr (owner_mem color l r)
    simp only [pack,if_pos rfl] at hn ⊢
    cases he : (pack color (owner color l r) l).join (pack color (owner color l r) r) <;>
      simp_all [Stored.addRoot,Stored.rootRecords,Source.rootRecord]

end ChaCha.Paper20261030.ColoredStorage
