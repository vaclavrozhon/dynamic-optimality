import DynamicOptimality.Funnel.Basic
import Mathlib.Order.Hom.Basic

/-!
# Funnels are invariant under increasing renumbering of occurrence times

Keeping an arbitrary set of occurrences at their old times is therefore
equivalent to reading the induced subsequence in consecutive time order.
-/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α] {m n : Nat}

theorem visible_reindex (word : Fin m → α) (times : Fin n ↪o Fin m)
    (active : Finset (Fin n)) (p q : Fin n) :
    Visible word (active.image times) (times p) (times q) ↔
      Visible (word ∘ times) active p q := by
  constructor
  · rintro ⟨hp,hq,qp,ne,empty⟩
    refine ⟨?_,?_,(times.lt_iff_lt).mp qp,ne,?_⟩
    · simpa [Finset.mem_image, times.injective.eq_iff] using hp
    · simpa [Finset.mem_image, times.injective.eq_iff] using hq
    · intro s hs qs sp
      exact empty (times s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
        (times.strictMono qs) (times.strictMono sp)
  · rintro ⟨hp,hq,qp,ne,empty⟩
    refine ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,Finset.mem_image.mpr ⟨q,hq,rfl⟩,
      times.strictMono qp,ne,?_⟩
    intro s hs qs sp
    obtain ⟨s,inside,rfl⟩ := Finset.mem_image.mp hs
    exact empty s inside ((times.lt_iff_lt).mp qs) ((times.lt_iff_lt).mp sp)

theorem switch_reindex (word : Fin m → α) (times : Fin n ↪o Fin m)
    (active : Finset (Fin n)) (p q r : Fin n) :
    Switch word (active.image times) (times p) (times q) (times r) ↔
      Switch (word ∘ times) active p q r := by
  constructor
  · rintro ⟨hp,hq,qr,sides,next⟩
    refine ⟨(visible_reindex word times active p q).mp hp,
      (visible_reindex word times active p r).mp hq,(times.lt_iff_lt).mp qr,sides,?_⟩
    intro s hs qs sr visible
    exact next (times s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
      (times.strictMono qs) (times.strictMono sr)
      ((visible_reindex word times active p s).mpr visible)
  · rintro ⟨hp,hq,qr,sides,next⟩
    refine ⟨(visible_reindex word times active p q).mpr hp,
      (visible_reindex word times active p r).mpr hq,times.strictMono qr,sides,?_⟩
    intro s hs qs sr visible
    obtain ⟨s,inside,rfl⟩ := Finset.mem_image.mp hs
    exact next s inside ((times.lt_iff_lt).mp qs) ((times.lt_iff_lt).mp sr)
      ((visible_reindex word times active p s).mp visible)

theorem count_reindex (word : Fin m → α) (times : Fin n ↪o Fin m)
    (active : Finset (Fin n)) :
    count word (active.image times) = count (word ∘ times) active := by
  unfold count
  symm
  apply Finset.card_bij (fun t _ => (times t.1,times t.2.1,times t.2.2))
  · intro t ht
    exact mem_switches.mpr ((switch_reindex word times active _ _ _).mpr (mem_switches.mp ht))
  · intro a ha b hb same
    have p : a.1 = b.1 := times.injective (congrArg Prod.fst same)
    have q : a.2.1 = b.2.1 := times.injective (congrArg (fun t => t.2.1) same)
    have r : a.2.2 = b.2.2 := times.injective (congrArg (fun t => t.2.2) same)
    exact Prod.ext p (Prod.ext q r)
  · rintro ⟨p,q,r⟩ ht
    have turn := mem_switches.mp ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp turn.1.1
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp turn.1.2.1
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp turn.2.1.2.1
    exact ⟨(p,q,r),mem_switches.mpr ((switch_reindex word times active p q r).mp turn),rfl⟩

theorem edgeCount_reindex (word : Fin m → α) (times : Fin n ↪o Fin m)
    (active : Finset (Fin n)) :
    edgeCount word (active.image times) = edgeCount (word ∘ times) active := by
  unfold edgeCount
  symm
  apply Finset.card_bij (fun e _ => (times e.1,times e.2))
  · intro e he
    exact mem_edges.mpr ((visible_reindex word times active _ _).mpr (mem_edges.mp he))
  · intro a ha b hb same
    exact Prod.ext (times.injective (congrArg Prod.fst same))
      (times.injective (congrArg Prod.snd same))
  · rintro ⟨q,p⟩ he
    have visible := mem_edges.mp he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp visible.1
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp visible.2.1
    exact ⟨(q,p),mem_edges.mpr ((visible_reindex word times active p q).mp visible),rfl⟩

end DynamicOptimality.Funnel
