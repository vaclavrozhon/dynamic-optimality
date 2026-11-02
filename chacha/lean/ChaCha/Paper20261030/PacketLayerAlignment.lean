import ChaCha.Paper20261030.LocalPacketLayerStaging

/-! Splitting and rebuilding mixed packet layers preserve the relation
between stored packet ids and the immutable id of the reached vertex.
No condition is imposed on the lengths of logical record lists here.
-/

namespace ChaCha.Paper20261030.PacketLayers

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketAlignment

variable {α ρ ι : Type*}

theorem aligned_append_iff (markerId vertexId : ι) (first last : Packet α ρ ι) :
    Aligned markerId vertexId (first++last) ↔ Aligned markerId vertexId first ∧ Aligned markerId vertexId last := by
  constructor
  · intro valid
    exact ⟨fun entry member => valid entry (List.mem_append_left last member),
      fun entry member => valid entry (List.mem_append_right first member)⟩
  · rintro ⟨firstValid,lastValid⟩
    exact PacketAlignment.append markerId vertexId first last firstValid lastValid

theorem aligned_cons_iff (markerId vertexId : ι) (entry : Option (Datum α ρ ι)) (rest : Packet α ρ ι) :
    Aligned markerId vertexId (entry::rest) ↔ Entry markerId vertexId entry ∧ Aligned markerId vertexId rest := by
  constructor
  · intro valid
    exact ⟨valid entry List.mem_cons_self,fun next member => valid next (List.mem_cons_of_mem entry member)⟩
  · rintro ⟨firstValid,lastValid⟩ next member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstValid
    · exact lastValid next member

theorem prepend_aligned (markerId vertexId : ι) (records : List ρ) (base : Packet α ρ ι) :
    Aligned markerId vertexId (PhysicalPacketStaging.Context.prependLogical records base) ↔ Aligned markerId vertexId base := by
  cases base with
  | nil => rfl
  | cons entry rest => cases entry with
    | none => rfl
    | some entry => cases entry with
      | header => rfl
      | real record =>
        rcases record with ⟨⟨id,tail⟩,fields⟩
        simp only [PhysicalPacketStaging.Context.prependLogical,aligned_cons_iff,Entry]

theorem stage_aligned (markerId vertexId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (aligned : Aligned markerId vertexId (stored base expression)) :
    Aligned markerId vertexId (staged markerId base expression) := by
  induction expression with
  | base => exact aligned
  | raw records rest ih =>
    obtain ⟨front,tail⟩ := (aligned_append_iff _ _ _ _).mp aligned
    exact PacketAlignment.append _ _ _ _ front (ih tail)
  | whole id records fields rest ih =>
    have tail := ((aligned_cons_iff _ _ _ _).mp aligned).2
    exact PacketAlignment.append _ _ _ _ (markers markerId records vertexId) (ih tail)
  | «prefix» records =>
    have baseValid := (prepend_aligned markerId vertexId records base).mp aligned
    exact PacketAlignment.append _ _ _ _ (markers markerId records vertexId) baseValid

theorem rebuilt_aligned (markerId vertexId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (aligned : Aligned markerId vertexId (staged markerId base expression)) :
    Aligned markerId vertexId (rebuilt vertexId base expression) := by
  induction expression with
  | base => exact aligned
  | raw records rest ih =>
    obtain ⟨front,tail⟩ := (aligned_append_iff _ _ _ _).mp aligned
    exact PacketAlignment.append _ _ _ _ front (ih tail)
  | whole id records fields rest ih =>
    have tail := ((aligned_append_iff _ _ _ _).mp aligned).2
    exact (aligned_cons_iff _ _ _ _).mpr ⟨Or.inr rfl,ih tail⟩
  | «prefix» records =>
    have baseValid := ((aligned_append_iff _ _ _ _).mp aligned).2
    exact (prepend_aligned markerId vertexId records base).mpr baseValid

end ChaCha.Paper20261030.PacketLayers
