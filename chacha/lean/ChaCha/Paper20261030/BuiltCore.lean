import ChaCha.Paper20261030.SecondaryCore
import ChaCha.Paper20261030.BalancedAssembly

/-!
# An initialized balanced secondary core

The core is constructed from the actual preferred reference path, using
the verified balanced assembly routine. Ordering, balance, interval
search correctness, and charged search bounds follow for this concrete
tree. The initialization trace starts from its existing records on a
right spine; it does not yet initialize the complete original-key BST.
-/

namespace ChaCha.Paper20261030.SecondaryCore

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open Auxiliary Auxiliary.Metadata

def build (start : Nat) {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :=
  assemble (word start reference preference)

theorem build_word (start : Nat) {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    (build start reference preference).impl.toListModel = word start reference preference :=
  assemble_word _

theorem build_ordered (start : Nat) {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    (build start reference preference).impl.Ordered := by
  simpa only [Impl.Ordered,build_word,Nat.compare_eq_lt] using keys_increasing start reference preference

theorem build_charged (start : Nat) {a b : Nat} (reference : DepthTree a b) (preference : DepthSplit → Bool) :
    ObservedRearranges (spine (word start reference preference)) (build start reference preference).impl
      ((495 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 78) *
        (word start reference preference).length) := by
  apply (assemble_charged (word start reference preference)).mono
  have hm := Nat.clog_monotone 2 (Nat.add_le_add_right (word_length start reference preference) 1)
  exact Nat.mul_le_mul_right _ (by omega)

theorem build_search_correct (d start : Nat) {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    lastGood (containsDepth d) (build start reference preference).impl =
      ((word start reference preference).filter (containsDepth d)).getLast? :=
  core_search_correct d start reference preference _ (build_word start reference preference)

theorem build_search_charged (d start : Nat) {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (ancestors) :
    ∃ cost, Trace ⟨recordTree (build start reference preference).impl,ancestors⟩
      (queryReads (containsDepth d) (build start reference preference).impl)
      ⟨recordTree (build start reference preference).impl,ancestors⟩ cost ∧
      cost ≤ 9 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) :=
  core_search_charged d start reference preference _ (build start reference preference).balanced_impl
    (build_word start reference preference) ancestors

end ChaCha.Paper20261030.SecondaryCore
