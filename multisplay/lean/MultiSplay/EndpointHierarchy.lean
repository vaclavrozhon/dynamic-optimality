import ChaCha.Reference
import MultiSplay.SecondaryRows
import MultiSplay.EndpointEncoding

/-!
# The doubled depth hierarchy for endpoint copies

An original depth below the reference height becomes two consecutive depths;
the final completion depth becomes a singleton. Every original interval split
is retained, with its cut immediately after the corresponding even depth.
The construction and its owner-row injection do not require balanced splits.
-/

namespace MultiSplay.EndpointHierarchy

open ChaCha (DepthSplit DepthTree)
open EndpointEncoding (core core_length core_injective)

def upper (height depth : Nat) : Nat := 2 * depth + if depth < height then 1 else 0

def split (height : Nat) (original : DepthSplit) : DepthSplit :=
  ⟨2 * original.lo, 2 * original.cut + 1, upper height original.hi⟩

def reindex {a b c d : Nat} (tree : DepthTree a b) (left : a = c) (right : b = d) : DepthTree c d :=
  left ▸ right ▸ tree

@[simp] theorem reindex_nodes {a b c d : Nat} (tree : DepthTree a b) (left : a = c) (right : b = d) :
    (reindex tree left right).nodes = tree.nodes := by
  subst c; subst d
  rfl

def expand (height : Nat) {a b : Nat} (tree : DepthTree a b) (bounded : b ≤ height) :
    DepthTree (2*a) (upper height b) :=
  match tree with
  | .leaf depth =>
      if inside : depth < height then
        reindex (.node (2*depth) (by omega) (by omega) (.leaf (2*depth)) (.leaf (2*depth+1)))
          rfl (by simp [upper, inside])
      else reindex (.leaf (2*depth)) rfl (by simp [upper, inside])
  | @DepthTree.node a b cut low high left right =>
      .node (2*cut+1) (by omega) (by unfold upper; split <;> omega)
        (reindex (expand height left (by omega)) rfl (by simp [upper, show cut < height by omega]))
        (reindex (expand height right bounded) (by omega) rfl)

/-- Every original split survives in the expanded hierarchy. -/
theorem split_mem {height a b : Nat} (tree : DepthTree a b) (bounded : b ≤ height)
    {original : DepthSplit} (member : original ∈ tree.nodes) :
    split height original ∈ (expand height tree bounded).nodes := by
  induction tree with
  | leaf depth => simp [DepthTree.nodes] at member
  | @node a b cut low high left right ihl ihr =>
      simp only [DepthTree.nodes, Finset.mem_insert, Finset.mem_union] at member
      simp only [expand, DepthTree.nodes, reindex_nodes, Finset.mem_insert, Finset.mem_union]
      rcases member with rfl | member | member
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (ihl (by omega) member))
      · exact Or.inr (Or.inr (ihr bounded member))

theorem upper_injective (height : Nat) : Function.Injective (upper height) := by
  intro a b same
  unfold upper at same
  split at same <;> split at same <;> omega

theorem split_injective (height : Nat) : Function.Injective (split height) := by
  intro a b same
  have lo := congrArg DepthSplit.lo same
  have cut := congrArg DepthSplit.cut same
  have hi := upper_injective height (congrArg DepthSplit.hi same)
  cases a; cases b
  simp only [split] at lo cut hi
  congr <;> omega

/-- Doubling preserves both interval membership and the written direction. -/
theorem split_contains (height : Nat) (original : DepthSplit) (depth : Nat) :
    ((split height original).lo ≤ 2*depth ∧ 2*depth ≤ (split height original).hi) ↔
      original.lo ≤ depth ∧ depth ≤ original.hi := by
  simp only [split, upper]
  split <;> omega

theorem split_direction (height : Nat) (original : DepthSplit) (depth : Nat) :
    ((split height original).cut < 2*depth) ↔ original.cut < depth := by
  simp only [split]
  omega

def row (height : Nat) (original : Secondary.Row) : Secondary.Row :=
  ⟨split height original.1, core original.2⟩

theorem row_injective (height : Nat) : Function.Injective (row height) := by
  rintro ⟨a,u⟩ ⟨b,v⟩ same
  have intervals := split_injective height (congrArg Sigma.fst same)
  have owners := core_injective (congrArg (fun entry : Secondary.Row => entry.2) same)
  change a = b at intervals
  change u = v at owners
  subst b; subst v
  rfl

theorem row_mem {height a b : Nat} (tree : DepthTree a b) (bounded : b ≤ height)
    {original : Secondary.Row} (member : original ∈ Secondary.rows tree) :
    row height original ∈ Secondary.rows (expand height tree bounded) := by
  simp only [Secondary.rows, Finset.mem_sigma, ChaCha.Primary.mem_level] at member ⊢
  exact ⟨split_mem tree bounded member.1, by simpa only [row, split, core_length] using congrArg (2*·) member.2⟩

/-- A hierarchy on depths 0 through H becomes one on depths 0 through 2H. -/
def doubled {height : Nat} (tree : DepthTree 0 height) : DepthTree 0 (2*height) :=
  reindex (expand height tree le_rfl) rfl (by simp [upper])

theorem doubled_row_mem {height : Nat} (tree : DepthTree 0 height)
    {original : Secondary.Row} (member : original ∈ Secondary.rows tree) :
    row height original ∈ Secondary.rows (doubled tree) := by
  simpa only [Secondary.rows, doubled, reindex_nodes] using row_mem tree le_rfl member

end MultiSplay.EndpointHierarchy
