import Splay.Accounting.ArticleRequestPreparation
import Splay.Accounting.ArticleSourcePairingGeometry

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST Splay.Lazy.Canonical

/-- The actual prepared source has the correct ambient order even when it
is not contiguous across left and right attachments. -/
theorem ArticleRequestPreparation.source_sublist {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    (preparation : ArticleRequestPreparation params snapshot before key initial)
    (rankZero : snapshot.rank (valuePos key) = 0)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (found : preparation.final.blocks[sourceId]? = some source)
    (owner : source.owner = valuePos key)
    (notLeft : sourceId ≠ preparation.leftId) (notRight : sourceId ≠ preparation.rightId) :
    source.elements.reverse.Sublist
      (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key.val 0) := by
  obtain ⟨removed, erased, fresh⟩ := exists_articleIsolatedBoundariesWitness snapshot before key rankZero
    preparation.represents preparation.leftFound preparation.leftElements
    preparation.rightFound preparation.rightElements found owner notLeft notRight
  have originalSegment :=
    (preparation.represents.valid.2 source (List.mem_of_getElem? found)).isSegment
  have retained := originalSegment.foldl_erase_ambient_of_fresh fresh
  rw [← erased] at retained
  have sourceSublist : source.elements.Sublist
      (rootHeavyPathCanonicalChildOrder snapshot before key.isLt rankZero).elements :=
    (IsSegment.sublist retained).trans List.filter_sublist
  simpa only [rootHeavyPathCanonicalChildOrder, rootHeavyPathChildrenBottomUp,
    rootHeavyPathChildrenTopDown, rootHeavyPathEdgesBottomUp, List.map_reverse] using sourceSublist.reverse


end Splay.Accounting
