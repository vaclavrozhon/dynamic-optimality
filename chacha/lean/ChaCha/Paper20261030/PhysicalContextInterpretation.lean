import ChaCha.Paper20261030.PhysicalComponentOperations
import ChaCha.Paper20261030.PackedContextReassembly

/-!
# Exposed packed contexts commute with original-key payload interpretation

Relabeling depth ports, mapping their records into physical datums, and
attaching the actual primary payloads all preserve the exposed context.
Only its connector lists are mapped into physical record prefixes. This
lets constant-size context reassembly operate on unchanged whole
original-key blocks, rather than on abstract depth labels.
-/

namespace ChaCha.Paper20261030.SourcePayloads

open ColoredStorage ProjectionLocal

variable {α β ρ : Type*}

theorem graft_prepend (payload : α → Source β (List (Option ρ))) (extras : List ρ)
    (source : Source α (List ρ)) :
    graft payload (prepend extras source) = prepend (extras.map some) (graft payload source) := by
  cases source with
  | leaf key records =>
    cases hp : payload key <;> simp [prepend,graft,hp,Source.setRoot,Source.rootRecord,List.map_append,List.append_assoc]
  | fork records l r =>
    simp only [prepend,graft,Source.setRoot,Source.rootRecord,List.map_append]

end ChaCha.Paper20261030.SourcePayloads

namespace ChaCha.Paper20261030.ProjectionLocal

open ColoredStorage

variable {α β γ ρ τ : Type*}

def interpret (payload : β → Source γ (List (Option τ))) (labels : α → β) (values : ρ → τ)
    (source : Projected α ρ) : Projected γ (Option τ) :=
  source.map (fun source => SourcePayloads.graft payload ((source.relabel labels).mapRecords (List.map values)))

theorem interpret_join (payload : β → Source γ (List (Option τ))) (labels : α → β) (values : ρ → τ)
    (left right : Projected α ρ) :
    interpret payload labels values (join left right) =
      join (interpret payload labels values left) (interpret payload labels values right) := by
  cases left <;> cases right <;> rfl

theorem interpret_decorate (payload : β → Source γ (List (Option τ))) (labels : α → β) (values : ρ → τ)
    (extras : List ρ) (source : Projected α ρ) :
    interpret payload labels values (decorate extras source) =
      decorate (extras.map (fun record => some (values record))) (interpret payload labels values source) := by
  cases source with
  | none => rfl
  | some source =>
    change some (SourcePayloads.graft payload
      (((prepend extras source).relabel labels).mapRecords (List.map values))) = _
    have relabel : (prepend extras source).relabel labels = prepend extras (source.relabel labels) := by
      cases source <;> rfl
    have mapRecords : (prepend extras (source.relabel labels)).mapRecords (List.map values) =
        prepend (extras.map values) ((source.relabel labels).mapRecords (List.map values)) := by
      cases source <;> simp [prepend,Source.relabel,Source.mapRecords,Source.rootRecord,Source.setRoot,List.map_append]
    rw [relabel,mapRecords,SourcePayloads.graft_prepend]
    simp only [interpret,decorate,prepend,Option.map_some,List.map_map,Function.comp_def]

theorem mirror_join (left right : Projected α ρ) : mirror (join left right) = join (mirror right) (mirror left) := by
  cases left <;> cases right <;> rfl

theorem mirror_decorate (records : List ρ) (source : Projected α ρ) :
    mirror (decorate records source) = decorate records (mirror source) := by
  cases source with
  | none => rfl
  | some source => cases source <;> rfl

end ChaCha.Paper20261030.ProjectionLocal

namespace ChaCha.Paper20261030.OrderedContext

open ColoredStorage ProjectionLocal

variable {ι α β γ ρ τ : Type*}

theorem interpret_decorated (payload : β → Source γ (List (Option τ))) (labels : α → β) (values : ρ → τ)
    (blocks : ι → Projected α ρ) (context : Source ι (List ρ)) :
    interpret payload labels values (decorated blocks context) =
      decorated (fun i => interpret payload labels values (blocks i))
        (context.mapRecords (List.map (fun record => some (values record)))) := by
  induction context with
  | leaf key records => exact interpret_decorate payload labels values records (blocks key)
  | fork records l r ihl ihr =>
    simp only [decorated,Source.mapRecords,interpret_decorate,interpret_join,ihl,ihr]

theorem mirror_decorated (blocks : ι → Projected α ρ) (context : Source ι (List ρ)) :
    mirror (decorated blocks context) = decorated (fun i => mirror (blocks i)) context.mirror := by
  induction context with
  | leaf key records => exact mirror_decorate records (blocks key)
  | fork records l r ihl ihr => simp only [decorated,Source.mirror,mirror_decorate,mirror_join,ihl,ihr]

end ChaCha.Paper20261030.OrderedContext
