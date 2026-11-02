import DynamicOptimality.MultiFinger.TendonPush

/-! Empty and singleton endpoints of source tendons.
Removing the last separator merely exposes its two existing subtrees;
creating a one-separator queue introduces no rotation or imbalance. -/

namespace DynamicOptimality.MultiFinger.TendonContents

open ChaCha.MTR SingleFinger
open DynamicOptimality.GeometricOnlineSimulation.OpenDeque
open TendonSource

variable {α : Type*}

theorem layout_singleton (layout : SingleFinger.Deque.Layout α) (key : α) (gap : RawTree α)
    (cells : layout.cells = [(key,gap)]) :
    layout.tree = .node layout.gap key gap ∧ layout.potential = 0 := by
  rcases layout with ⟨first,front,pivot,after,back⟩
  have lengths := congrArg List.length cells
  simp only [SingleFinger.Deque.Layout.cells,List.length_append,List.length_cons,List.length_nil] at lengths
  have frontNil : front = [] := List.eq_nil_of_length_eq_zero (by omega)
  have backNil : back = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst front
  subst back
  have entry : (pivot,after) = (key,gap) := by simpa only [SingleFinger.Deque.Layout.cells,List.nil_append,List.cons.injEq,and_true] using cells
  have keyEq : pivot = key := congrArg Prod.fst entry
  have gapEq : after = gap := congrArg Prod.snd entry
  subst pivot
  subst after
  exact ⟨rfl,rfl⟩

theorem low_singleton (layout : Right α) (key : α) (gap : RawTree α)
    (valid : LowValid layout [(gap,key)]) (inside : RawTree α) :
    (layout.fill inside).tree = .node gap key inside ∧ layout.potential = 0 := by
  have entries : (layout.fill inside).cells = [(key,inside)] := (valid inside).2
  have result := layout_singleton (layout.fill inside) key inside entries
  simpa only [(valid inside).1,firstGap,Right.fill_potential] using result

theorem high_singleton (layout : Left α) (key : α) (gap : RawTree α)
    (valid : HighValid layout [(key,gap)]) (inside : RawTree α) :
    (layout.fill inside).tree = .node inside key gap ∧ layout.potential = 0 := by
  have result := layout_singleton (layout.fill inside) key gap (valid inside)
  have initial : (layout.fill inside).gap = inside := rfl
  simpa only [initial,Left.fill_potential] using result

theorem low_singleton_create (key : α) (gap : RawTree α) :
    ∃ layout : Right α, LowValid layout [(gap,key)] ∧ layout.potential = 0 ∧
      ∀ inside, (layout.fill inside).tree = .node gap key inside := by
  exact ⟨⟨gap,[],key,none⟩,by intro inside; exact ⟨rfl,rfl⟩,rfl,fun _ => rfl⟩

theorem high_singleton_create (key : α) (gap : RawTree α) :
    ∃ layout : Left α, HighValid layout [(key,gap)] ∧ layout.potential = 0 ∧
      ∀ inside, (layout.fill inside).tree = .node inside key gap := by
  exact ⟨⟨[],key,gap,[]⟩,fun _ => rfl,rfl,fun _ => rfl⟩

end DynamicOptimality.MultiFinger.TendonContents
