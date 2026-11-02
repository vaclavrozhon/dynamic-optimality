import DynamicOptimality.MultiFinger.Hand

/-! Local source changes when a finger crosses one ordinary tree edge.
The source tree remains fixed. Only the two endpoint mark statuses change:
first retain the destination, then release the old position if no finger
remains there. These source identities do not assert a physical simulation
cost; the persistent deque and top-splay lemmas must supply that cost. -/

namespace DynamicOptimality.MultiFinger.Hand

open ChaCha.MTR

variable {α : Type*}

def assemble (marked : Bool) (left : Hand α) (key : α) (right : Hand α) : Hand α :=
  if marked || (left.nonempty && right.nonempty) then .node [] left key right
  else if left.nonempty then left.extend (.left key right.source)
  else if right.nonempty then right.extend (.right left.source key)
  else .stump (.node left.source key right.source)

@[simp] theorem assemble_source (marked : Bool) (left : Hand α) (key : α) (right : Hand α) :
    (assemble marked left key right).source = .node left.source key right.source := by
  simp only [assemble]
  split
  · rfl
  · split
    · simp only [extend_source,Pointer.plug]
    · split
      · simp only [extend_source,Pointer.plug]
      · rfl

@[simp] theorem assemble_marked (left : Hand α) (key : α) (right : Hand α) :
    assemble true left key right = .node [] left key right := rfl

theorem assemble_core (marked : Bool) (left : Hand α) (key : α) (right : Hand α) :
    (assemble marked left key right).core = Steiner.merge marked left.core key right.core := by
  simp only [assemble,Steiner.merge,present_core]
  split
  · rfl
  · split
    · exact extend_core _ _
    · split
      · exact extend_core _ _
      · cases right <;> simp_all [nonempty,core]

theorem root_mark_size (left : Hand α) (key : α) (right : Hand α) :
    (assemble false left key right).core.size ≤ (assemble true left key right).core.size ∧
      (assemble true left key right).core.size ≤ (assemble false left key right).core.size+1 := by
  cases left <;> cases right <;>
    simp [assemble,nonempty,core,extend,Tree.size] <;> omega

theorem compress_assemble (marked : α → Bool) (left : RawTree α) (key : α) (right : RawTree α) :
    compress marked (.node left key right) =
      assemble (marked key) (compress marked left) key (compress marked right) := by
  simp only [compress,assemble,compress_source]

/-- Moving a finger to the right child changes at most the two endpoint
statuses. Multiplicity is represented by `keepParent` and `alreadyChild`;
all three hanging source subtrees are preserved literally. -/
theorem right_edge_source (keepParent alreadyChild : Bool)
    (left middle right : Hand α) (parent child : α) :
    (assemble true left parent (assemble alreadyChild middle child right)).source =
      (assemble keepParent left parent (assemble true middle child right)).source := by
  simp only [assemble_source]

theorem left_edge_source (keepParent alreadyChild : Bool)
    (left middle right : Hand α) (child parent : α) :
    (assemble true (assemble alreadyChild left child middle) parent right).source =
      (assemble keepParent (assemble true left child middle) parent right).source := by
  simp only [assemble_source]

/-- Promotion of the parent immediately above the inner tendon endpoint.
No interior tendon position is split. -/
theorem promote_inner_left (frames : List (Pointer.Frame α))
    (left right : Hand α) (key parent : α) (sibling : RawTree α) :
    (Hand.node (.left parent sibling::frames) left key right).source =
      (Hand.node frames (.node [] left key right) parent (.stump sibling)).source := rfl

theorem promote_inner_right (frames : List (Pointer.Frame α))
    (left right : Hand α) (key parent : α) (sibling : RawTree α) :
    (Hand.node (.right sibling parent::frames) left key right).source =
      (Hand.node frames (.stump sibling) parent (.node [] left key right)).source := rfl

/-- Promotion of the outer endpoint is the other deque end. -/
theorem promote_outer_left (frames : List (Pointer.Frame α))
    (left right : Hand α) (key parent : α) (sibling : RawTree α) :
    (Hand.node (frames++[.left parent sibling]) left key right).source =
      (Hand.node [] (.node frames left key right) parent (.stump sibling)).source := by
  simp only [source,plug_append,Pointer.plug]

theorem promote_outer_right (frames : List (Pointer.Frame α))
    (left right : Hand α) (key parent : α) (sibling : RawTree α) :
    (Hand.node (frames++[.right sibling parent]) left key right).source =
      (Hand.node [] (.stump sibling) parent (.node frames left key right)).source := by
  simp only [source,plug_append,Pointer.plug]

end DynamicOptimality.MultiFinger.Hand
