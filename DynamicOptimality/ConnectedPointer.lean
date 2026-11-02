import DynamicOptimality.PointerOptimum
import DynamicOptimality.HullPointer
import Splay.Accounting.OfflineConnectedNormalization

/-!
# A pointer realization of the shared offline optimum

The splay development already proves that rotations outside the connected
support of a request can be postponed. We translate its actual selected
prefixes into Cha-Cha's marked hulls, preserving both the selected keys and
all untouched hanging subtrees. The existing hull simulation then gives
an adjacent-pointer execution within a universal factor of the same OPT.
-/

namespace DynamicOptimality

open ChaCha ChaCha.MTR ChaCha.MTR.Pointer
open Splay.Accounting.OfflineConnectedSupport

def markPrefix : {lower upper : Nat} → {t : DynamicOptimality.BST lower upper} →
    RootPrefix t → MarkedTree Nat
  | _, _, _, .none t => .hole (DynamicOptimality.BST.toRaw t)
  | _, _, _, .node (root := key) l r => .node (markPrefix l) key (markPrefix r)

theorem markPrefix_erase {lower upper : Nat} {t : DynamicOptimality.BST lower upper}
    (p : RootPrefix t) : (markPrefix p).erase = (DynamicOptimality.BST.toRaw t) := by
  induction p <;> simp [markPrefix,MarkedTree.erase,BST.toRaw, *]

theorem markPrefix_size {lower upper : Nat} {t : DynamicOptimality.BST lower upper}
    (p : RootPrefix t) : MTR.Tree.size (markPrefix p).skeleton = p.card := by
  induction p <;> simp [markPrefix,MarkedTree.skeleton,MTR.Tree.size,RootPrefix.card, *]

theorem supported_marks {depth lower upper : Nat} {t u : DynamicOptimality.BST lower upper}
    {rotation : Splay.Tree.BST.RotationAt depth t u} {p : RootPrefix t} {q : RootPrefix u}
    (supported : SupportedRotation rotation p q) :
    (markPrefix p).holes = (markPrefix q).holes ∧
      MTR.Tree.inorder (markPrefix p).skeleton = MTR.Tree.inorder (markPrefix q).skeleton := by
  induction supported with
  | rootRight => simp [markPrefix,MarkedTree.holes,MarkedTree.skeleton,MTR.Tree.inorder,List.append_assoc]
  | rootLeft => simp [markPrefix,MarkedTree.holes,MarkedTree.skeleton,MTR.Tree.inorder,List.append_assoc]
  | leftContext rotation supported right rightPrefix ih =>
    simp only [markPrefix,MarkedTree.holes,MarkedTree.skeleton,MTR.Tree.inorder,ih.1,ih.2,and_self]
  | rightContext left leftPrefix rotation supported ih =>
    simp only [markPrefix,MarkedTree.holes,MarkedTree.skeleton,MTR.Tree.inorder,ih.1,ih.2,and_self]

theorem supported_execution_marks {length lower upper : Nat} {t u : DynamicOptimality.BST lower upper}
    {p : RootPrefix t} {q : RootPrefix u} (supported : SupportedRotationExecution length p q) :
    (markPrefix p).holes = (markPrefix q).holes ∧
      MTR.Tree.inorder (markPrefix p).skeleton = MTR.Tree.inorder (markPrefix q).skeleton := by
  induction supported with
  | refl => exact ⟨rfl,rfl⟩
  | step rotation support tail ih =>
    have first := supported_marks support
    exact ⟨first.1.trans ih.1,first.2.trans ih.2⟩

theorem markPrefix_root_mem {lower upper key : Nat} {t : DynamicOptimality.BST lower upper}
    (p : RootPrefix t) (positive : 0 < p.card) (root : t.HasRoot key) :
    key ∈ MTR.Tree.inorder (markPrefix p).skeleton := by
  have hr : MTR.Tree.rootKey (DynamicOptimality.BST.toRaw t) = some key := by
    obtain ⟨l,r,rfl⟩ := root
    rfl
  cases p with
  | none => simp [RootPrefix.card] at positive
  | @node lower root upper left right lp rp =>
    have hk := Option.some.inj hr
    subst key
    simp [markPrefix,MarkedTree.skeleton,MTR.Tree.inorder]

theorem supported_hull {length lower upper key : Nat} {t u : DynamicOptimality.BST lower upper}
    {p : RootPrefix t} {q : RootPrefix u} (supported : SupportedRotationExecution length p q)
    (positive : 0 < p.card) (root : u.HasRoot key) :
    ∃ access : HullAccess key (DynamicOptimality.BST.toRaw t) (DynamicOptimality.BST.toRaw u), access.cost = p.card := by
  have words := supported_execution_marks supported
  have qp : 0 < q.card := by rw [← supported.card_eq]; exact positive
  have requested := markPrefix_root_mem q qp root
  rw [← words.2] at requested
  refine ⟨{
    source := (markPrefix p).skeleton
    target := (markPrefix q).skeleton
    gaps := (markPrefix p).gapArray
    source_tree := (markPrefix p).graft_gapArray.trans (markPrefix_erase p)
    target_tree := ?_
    same_keys := words.2
    requested := requested
  },markPrefix_size p⟩
  have sameGaps : (markPrefix p).gapArray = (markPrefix q).gapArray := by
    funext i
    simp only [MarkedTree.gapArray,words.1]
  rw [sameGaps]
  exact (markPrefix q).graft_gapArray.trans (markPrefix_erase q)

theorem connected_hull {n rotations supportCharge : Nat} {requests : List (Fin n)}
    {t u : DynamicOptimality.BST 0 n}
    (execution : ConnectedExecution requests t u rotations supportCharge) :
    AccessExecution (DynamicOptimality.BST.toRaw t) (requests.map Fin.val) (DynamicOptimality.BST.toRaw u) supportCharge := by
  induction execution with
  | done => exact .nil _
  | next supported positive root tail ih =>
    obtain ⟨access,hcost⟩ := supported_hull supported positive root
    simpa only [List.map_cons,hcost] using AccessExecution.cons access ih

/-- The freely chosen initial tree is preserved by normalization. The
pointer trace serves exactly the original requests on the same key set. -/
theorem exists_pointer_of_OPT {n : Nat} (requests : List (Fin n)) :
    ∃ (initial : DynamicOptimality.BST 0 n) (final : RawTree Nat) (cost : Nat),
      PointerExecution (DynamicOptimality.BST.toRaw initial) (requests.map Fin.val) final cost ∧
      cost ≤ 37 * OPT requests := by
  obtain ⟨initial,final,rotations,execution,optimal⟩ := OPT_attained requests
  obtain ⟨last,kept,support,connected,hkept,hsupport⟩ := exists_connectedReordered execution
  obtain ⟨cost,pointer,hcost⟩ := accessExecution_pointer (connected_hull connected) (DynamicOptimality.BST.toRaw_ordered initial)
  refine ⟨initial,(DynamicOptimality.BST.toRaw last),cost,pointer,?_⟩
  omega

end DynamicOptimality
