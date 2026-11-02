import ChaCha.Paper20261030.ColoredStorage
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.WithBot

/-!
# Constant-size storage for virtual leaves

Give virtual leaves a separate color `none`; a real leaf has color
`some c`. Apply the checked colored packing and flatten its virtual-color
projection into a header. With `r` virtual leaves and `c` real colors, this
header contains at most `2*r*(c+1)` records. Each real projection vertex
holds at most `c+1` records. The construction preserves every source
record, including virtual-leaf descriptors, without adding a virtual leaf
to a real projection.

This is a storage theorem. Charged dynamic relocation of header records
under rotations remains a separate obligation.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open RouterProjection

variable {α ρ C : Type*}

local instance [LinearOrder C] : LinearOrder (Option C) :=
  inferInstanceAs (LinearOrder (WithBot C))

def Stored.vertexCount : Stored α ρ → Nat
  | .empty => 0
  | .leaf _ _ => 1
  | .fork _ l r => l.vertexCount + r.vertexCount + 1

theorem Stored.vertexCount_shape (t : Stored α ρ) :
    t.vertexCount = Router.internalCount t.shape + t.shape.leaves.length := by
  induction t with
  | empty => rfl
  | leaf => rfl
  | fork records l r ihl ihr =>
    simp only [vertexCount,shape,Router.internalCount,RouterProjection.Router.leaves,
      List.length_append,ihl,ihr]
    omega

theorem Stored.vertexCount_le (t : Stored α ρ) (h : Router.Full t.shape) :
    t.vertexCount ≤ 2 * t.shape.leaves.length := by
  by_cases he : t.shape = .empty
  · have ht := (Stored.shape_eq_empty t).mp he
    subst t
    exact le_rfl
  · have hc := Router.full_leaf_count t.shape h he
    rw [vertexCount_shape]
    omega

theorem Stored.records_card_le {t : Stored α ρ} {capacity : Nat}
    (h : t.Bounded capacity) : t.records.card ≤ capacity * t.vertexCount := by
  induction t with
  | empty => exact le_rfl
  | leaf key records => simpa [Stored.records,vertexCount,Stored.Bounded] using h
  | fork records l r ihl ihr =>
    have hl := ihl h.2.1
    have hr := ihr h.2.2
    have hs := h.1
    simp only [Stored.records,Multiset.card_add,Multiset.coe_card,vertexCount,
      Nat.mul_add,Nat.mul_one]
    omega

theorem pack_records_card_le [LinearOrder C] [Fintype C]
    (color : α → C) (q : C) (t : Source α ρ) :
    (pack color q t).records.card ≤ Fintype.card C *
      (2 * (t.shape.leaves.filter (fun key => decide (color key = q))).length) := by
  have hb := Stored.records_card_le (pack_bounded_colors color q t)
  have hf : Router.Full (pack color q t).shape := by
    rw [pack_shape]
    exact Router.full_prune _ _
  have hv := Stored.vertexCount_le (pack color q t) hf
  have hm := Nat.mul_le_mul_left (Fintype.card C) hv
  have bound := hb.trans hm
  simpa only [pack_shape,RouterProjection.Router.leaves_prune] using bound

def Stored.recordList : Stored α ρ → List ρ
  | .empty => []
  | .leaf _ records => records
  | .fork records l r => records ++ l.recordList ++ r.recordList

theorem Stored.recordList_multiset (t : Stored α ρ) :
    (t.recordList : Multiset ρ) = t.records := by
  induction t <;> simp_all [recordList,records,← Multiset.coe_add,add_assoc]

theorem Stored.recordList_length (t : Stored α ρ) :
    t.recordList.length = t.records.card := by
  rw [← recordList_multiset]
  rfl

def virtualCount (color : α → Option C) (t : Source α ρ) : Nat :=
  (t.shape.leaves.filter (fun key => (color key).isNone)).length

def headerRecords [LinearOrder C] (color : α → Option C) (t : Source α ρ) : List ρ :=
  (pack color none t).recordList

theorem header_size [LinearOrder C] [Fintype C] (color : α → Option C) (t : Source α ρ) :
    (headerRecords color t).length ≤ (Fintype.card C + 1) * (2 * virtualCount color t) := by
  have hb := pack_records_card_le color none t
  have he : (fun key => decide (color key = none)) = (fun key => (color key).isNone) := by
    funext key
    cases color key <;> rfl
  simpa only [headerRecords,Stored.recordList_length,Fintype.card_option,virtualCount,
    he] using hb

theorem header_and_real_records [LinearOrder C] [Fintype C]
    (color : α → Option C) (t : Source α ρ) :
    (headerRecords color t : Multiset ρ) +
      ∑ q : C, (pack color (some q) t).records = t.records := by
  simpa only [Fintype.sum_option,headerRecords,Stored.recordList_multiset] using
    pack_records_sum color t

theorem real_vertex_capacity [LinearOrder C] [Fintype C]
    (color : α → Option C) (q : C) (t : Source α ρ) :
    (pack color (some q) t).Bounded (Fintype.card C + 1) := by
  simpa only [Fintype.card_option] using pack_bounded_colors color (some q) t

end ChaCha.Paper20261030.ColoredStorage
