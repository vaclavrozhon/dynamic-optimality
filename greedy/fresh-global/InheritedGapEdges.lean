import ActualLinkRuns
import HeapSubtreeGeometry
import Splay.Accounting.WholeSplayHeapLinks

/-! Old edges with a nonaccess parent occur inside literal off-path gaps.
Those exact subtrees, and hence those exact parent-child incidences,
survive every separator refinement used by the actual access expansion. -/
namespace GreedyMerge.InheritedGapEdges
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.SearchGaps GreedyMerge.PathPlateau GreedyMerge.ExpansionRotations
open GreedyMerge.ExpandedFringe GreedyMerge.AccessFrontier
open GreedyMerge.HeapGeometry

theorem SearchGap.maximal {access innerLo innerHi lo hi : ℕ}
    {inner : BST innerLo innerHi} {tree : BST lo hi} (gap : SearchGap access inner tree) :
    (innerLo=lo ∨ innerLo-1 ∈ PathKeys access tree) ∧
    (innerHi=hi ∨ innerHi ∈ PathKeys access tree) ∧
    (∀ key, innerLo ≤ key → key < innerHi → key ∉ PathKeys access tree) := by
  induction gap with
  | @leftGap lo root hi left right outside =>
      refine ⟨Or.inl rfl,Or.inr (root_mem_pathKeys left right),?_⟩
      intro key lower upper member
      have direction := (pathKeys_left_iff left right upper).mp member
      omega
  | @rightGap lo root hi left right outside =>
      refine ⟨Or.inr ?_,Or.inl rfl,?_⟩
      · simpa using root_mem_pathKeys (access := access) left right
      · intro key lower upper member
        have direction := (pathKeys_right_iff left right (by omega)).mp member
        omega
  | @left innerLo innerHi lo root hi inner left right direction inside ih =>
      have bounds := (Classical.choose_spec inside.occurrence).bounds
      have ib := inner.lower_le_upper
      refine ⟨?_,?_,?_⟩
      · rcases ih.1 with equal | member
        · exact Or.inl equal
        · exact Or.inr ((pathKeys_left_iff left right (by
            have := pathKeys_bounds left member; omega)).mpr ⟨direction,member⟩)
      · rcases ih.2.1 with equal | member
        · exact Or.inr (by rw [equal]; exact root_mem_pathKeys left right)
        · exact Or.inr ((pathKeys_left_iff left right (by
            have := pathKeys_bounds left member; omega)).mpr ⟨direction,member⟩)
      · intro key lower upper member
        exact ih.2.2 key lower upper ((pathKeys_left_iff left right (by omega)).mp member).2
  | @right innerLo innerHi lo root hi inner left right direction inside ih =>
      have bounds := (Classical.choose_spec inside.occurrence).bounds
      have ib := inner.lower_le_upper
      refine ⟨?_,?_,?_⟩
      · rcases ih.1 with equal | member
        · right
          rw [equal]
          simpa using root_mem_pathKeys (access := access) left right
        · exact Or.inr ((pathKeys_right_iff left right (by
            have := pathKeys_bounds right member; omega)).mpr ⟨direction,member⟩)
      · rcases ih.2.1 with equal | member
        · exact Or.inl equal
        · exact Or.inr ((pathKeys_right_iff left right (by
            have := pathKeys_bounds right member; omega)).mpr ⟨direction,member⟩)
      · intro key lower upper member
        exact ih.2.2 key lower upper ((pathKeys_right_iff left right (by omega)).mp member).2

/-- Every literal maximal gap has exactly one enumerated separator slot. -/
theorem searchGap_interval_slot {n access lo hi : ℕ} {tree : BST 0 n}
    (p : Decomposition tree access) (gap : BST lo hi) (actual : SearchGap access gap tree) :
    ∃ i, i ≤ p.count ∧ lo=GapLower 0 p.separator i ∧ hi=p.separator i := by
  have maximal := SearchGap.maximal actual
  have order := gap.lower_le_upper
  obtain ⟨i,ib,upper⟩ : ∃ i, i ≤ p.count ∧ hi=p.separator i := by
    rcases maximal.2.1 with endpoint | member
    · exact ⟨p.count,le_rfl,endpoint.trans p.endpoint.symm⟩
    · obtain ⟨i,ib,equal⟩ := p.complete hi member
      exact ⟨i,Nat.le_of_lt ib,equal⟩
  refine ⟨i,ib,?_,upper⟩
  cases i with
  | zero =>
      change lo=0
      rcases maximal.1 with lower | member
      · exact lower
      · by_cases zero : lo=0
        · exact zero
        · obtain ⟨j,jb,key⟩ := p.complete (lo-1) member
          have mono := p.increasing.monotone (Nat.zero_le j)
          omega
  | succ i =>
      change lo=p.separator i+1
      have prior := p.member i (by omega)
      have strict := p.increasing (show i < i+1 from by omega)
      have below : p.separator i<lo := by
        by_contra no
        exact maximal.2.2 (p.separator i) (by omega) (by omega) prior
      rcases maximal.1 with lower | member
      · omega
      · obtain ⟨j,jb,key⟩ := p.complete (lo-1) member
        have jle : j ≤ i := by
          by_contra no
          have mono := p.increasing.monotone (show i+1 ≤ j by omega)
          omega
        have mono := p.increasing.monotone jle
        omega

/-- A concrete BST contains at most one subtree on a fixed indexed interval. -/
theorem subtree_same_interval {lo hi outerLo outerHi firstDepth secondDepth : ℕ}
    {first second : BST lo hi} {tree : BST outerLo outerHi}
    (one : SubtreeAt first firstDepth tree) (two : SubtreeAt second secondDepth tree) :
    first=second := by
  induction one generalizing second secondDepth with
  | here =>
      cases two with
      | here => rfl
      | left inside right =>
          have bounds := inside.bounds
          have other := right.lower_le_upper
          omega
      | right left inside =>
          have bounds := inside.bounds
          have other := left.lower_le_upper
          omega
  | left inside right ih =>
      cases two with
      | here =>
          have bounds := inside.bounds
          have other := right.lower_le_upper
          omega
      | left secondInside _ => exact ih secondInside
      | right left secondInside =>
          have oneBounds := inside.bounds
          have twoBounds := secondInside.bounds
          have order := first.lower_le_upper
          omega
  | right left inside ih =>
      cases two with
      | here =>
          have bounds := inside.bounds
          have other := left.lower_le_upper
          omega
      | left secondInside right =>
          have oneBounds := inside.bounds
          have twoBounds := secondInside.bounds
          have order := first.lower_le_upper
          omega
      | right _ secondInside => exact ih secondInside

theorem hasPair_depth {n lo hi firstDepth secondDepth parent child : ℕ}
    (snapshot : Snapshot n) (tree : BST lo hi) (upper : hi ≤ n) :
    HasPair snapshot tree upper firstDepth parent child ↔
      HasPair snapshot tree upper secondDepth parent child := by
  have same := Splay.Accounting.treeEdges_heapLink_depth_eq snapshot tree upper firstDepth secondDepth
  have character : ∀ depth,
      HasPair snapshot tree upper depth parent child ↔
        ∃ pair ∈ (treeEdges snapshot tree upper depth).map Splay.Accounting.heapLink,
          pair.1.val=parent ∧ pair.2.val=child := by
    intro depth
    simp only [HasPair,List.mem_map]
    constructor
    · rintro ⟨edge,member,hp,hc⟩
      exact ⟨_,⟨edge,member,rfl⟩,hp,hc⟩
    · rintro ⟨pair,⟨edge,member,rfl⟩,hp,hc⟩
      exact ⟨edge,member,hp,hc⟩
  rw [character,character,same]

theorem hasPair_subtree {n lo hi innerLo innerHi subtreeDepth depth parent child : ℕ}
    (snapshot : Snapshot n) {inner : BST innerLo innerHi} {tree : BST lo hi}
    (occurrence : SubtreeAt inner subtreeDepth tree) (upper : hi ≤ n)
    (member : HasPair snapshot inner (occurrence.bounds.2.trans upper) 0 parent child) :
    HasPair snapshot tree upper depth parent child := by
  have shifted := (hasPair_depth (firstDepth := 0) (secondDepth := depth+subtreeDepth)
    snapshot inner (occurrence.bounds.2.trans upper)).mp member
  obtain ⟨edge,edgeMem,hp,hc⟩ := shifted
  exact ⟨edge,subtree_edge_mem snapshot occurrence upper depth edge edgeMem,hp,hc⟩

/-- Every old maximal gap is the exact stored gap, not merely a shape
with the same key interval. -/
theorem searchGap_hasPair_slot {n access lo hi parent child : ℕ} (snapshot : Snapshot n)
    {tree : BST 0 n} (p : Decomposition tree access) (gap : BST lo hi)
    (actual : SearchGap access gap tree) (upper : hi ≤ n)
    (member : HasPair snapshot gap upper 0 parent child) :
    ∃ i, ∃ bound : i ≤ p.count,
      HasPair snapshot (p.gaps i) (by have h := p.increasing.monotone bound; rw [p.endpoint] at h; exact h)
        0 parent child := by
  obtain ⟨i,ib,lower,higher⟩ := searchGap_interval_slot p gap actual
  subst lo
  subst hi
  obtain ⟨oldDepth,oldOccurrence⟩ := actual.occurrence
  obtain ⟨gapDepth,gapOccurrence⟩ := (p.actualGap i ib).occurrence
  have equal := subtree_same_interval oldOccurrence gapOccurrence
  exact ⟨i,ib,by simpa only [equal] using member⟩

theorem gap_occurs_in_expansion {start lo hi i : ℕ} (separator : ℕ → ℕ)
    (gaps : ∀ index, BST (GapLower start separator index) (separator index))
    (skeleton : BST lo hi) (lower : lo ≤ i) (upper : i ≤ hi) :
    ∃ depth, SubtreeAt (gaps i) depth (Expand start separator gaps skeleton) := by
  induction skeleton with
  | empty index =>
      have same : i=index := by omega
      subst i
      exact ⟨0,.here⟩
  | @node lo root hi left right ihLeft ihRight =>
      by_cases inLeft : i ≤ root
      · obtain ⟨depth,occurrence⟩ := ihLeft lower inLeft
        exact ⟨depth+1,.left occurrence _⟩
      · obtain ⟨depth,occurrence⟩ := ihRight (by omega) upper
        exact ⟨depth+1,.right _ occurrence⟩

theorem nonaccess_edge_in_searchGap {n lo hi access parent child : ℕ}
    (snapshot : Snapshot n) (tree : BST lo hi) (upper : hi ≤ n) (depth : ℕ)
    (record : External n) (real : record.val=2*access+1) (zero : snapshot.rank record=0)
    (accessLo : lo ≤ access) (accessHi : access < hi) (different : parent ≠ record.val)
    (member : HasPair snapshot tree upper depth parent child) :
    ∃ gapLo gapHi, ∃ gap : BST gapLo gapHi, SearchGap access gap tree ∧
      ∃ gapUpper : gapHi ≤ n, HasPair snapshot gap gapUpper 0 parent child := by
  induction tree generalizing depth with
  | empty => omega
  | @node lo root hi left right ihLeft ihRight =>
      have leftBound := left.lower_le_upper
      have rightBound := right.lower_le_upper
      have rootUpper : root ≤ n := by omega
      let node : AtNode n := ⟨lo,root,hi,left,right,upper⟩
      have nodeOwner : node.owner snapshot=record :=
        owner_eq_of_zero snapshot (.node left right) upper record zero (by omega)
      obtain ⟨edge,edgeMem,ownerEq,childEq⟩ := member
      change edge ∈ edgesAtNode snapshot node depth ++
        treeEdges snapshot left rootUpper (depth+1) ++ treeEdges snapshot right upper (depth+1) at edgeMem
      rcases List.mem_append.mp edgeMem with beforeRight | rightMem
      · rcases List.mem_append.mp beforeRight with localMem | leftMem
        · have valid := mem_edgesAtNode_valid snapshot node depth localMem
          exact False.elim (different (ownerEq.symm.trans (congrArg Fin.val (valid.2.1.trans nodeOwner))))
        · have inside : HasPair snapshot left rootUpper (depth+1) parent child :=
            ⟨edge,leftMem,ownerEq,childEq⟩
          by_cases onPath : access<root
          · obtain ⟨a,b,gap,actual,gapUpper,pair⟩ := ihLeft rootUpper (depth+1) accessLo onPath inside
            exact ⟨a,b,gap,.left right onPath actual,gapUpper,pair⟩
          · exact ⟨lo,root,left,.leftGap left right (by omega),rootUpper,
              (hasPair_depth snapshot left rootUpper).mp inside⟩
      · have inside : HasPair snapshot right upper (depth+1) parent child :=
          ⟨edge,rightMem,ownerEq,childEq⟩
        by_cases onPath : root<access
        · obtain ⟨a,b,gap,actual,gapUpper,pair⟩ := ihRight upper (depth+1) (by omega) accessHi inside
          exact ⟨a,b,gap,.right left onPath actual,gapUpper,pair⟩
        · exact ⟨root+1,hi,right,.rightGap left right (by omega),upper,
            (hasPair_depth snapshot right upper).mp inside⟩

/-- Every old parent-child edge not owned by the access record survives
in the exact expanded new tree. No inherited-edge premise is assumed. -/
theorem inherited_edge_survives {n access parent child : ℕ} (snapshot : Snapshot n)
    (oldTree : BST 0 n) (p : Decomposition oldTree access) (skeleton : BST 0 p.count)
    (record : External n) (real : record.val=2*access+1) (zero : snapshot.rank record=0)
    (accessBound : access<n) (different : parent ≠ record.val)
    (member : HasPair snapshot oldTree (Nat.le_refl n) 0 parent child) :
    HasPair snapshot (p.expand skeleton) (Nat.le_refl n) 0 parent child := by
  obtain ⟨lo,hi,gap,actual,upper,pair⟩ := nonaccess_edge_in_searchGap snapshot oldTree
    (Nat.le_refl n) 0 record real zero (Nat.zero_le access) accessBound different member
  obtain ⟨i,ib,pairInGap⟩ := searchGap_hasPair_slot snapshot p gap actual upper pair
  obtain ⟨depth,occurrence⟩ := gap_occurs_in_expansion p.separator p.gaps skeleton (Nat.zero_le i) ib
  have topUpper : p.separator p.count ≤ n := by rw [p.endpoint]
  have inherited := hasPair_subtree snapshot occurrence topUpper pairInGap (depth := 0)
  exact (hasPair_castUpper snapshot p.endpoint _ _ (Nat.le_refl n) 0 parent child).mpr inherited

end GreedyMerge.InheritedGapEdges

#print axioms GreedyMerge.InheritedGapEdges.searchGap_interval_slot

#print axioms GreedyMerge.InheritedGapEdges.searchGap_hasPair_slot

#print axioms GreedyMerge.InheritedGapEdges.inherited_edge_survives
