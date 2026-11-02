import ChaCha.Paper20261030.SourcePayloads

/-!
# Moving the parent attachment prefix with a changing payload root

A child primary component can rearrange its own representation while its
parent's depth-slot metadata remains a prefix at the component root.
Read and remove that prefix, run the child operation, and restore it at
the reached new root. This adds four operations independent of the child
size. Both the source prefix and the payload record suffix are obtained
by decoding the actually reached record.
-/

namespace ChaCha.Paper20261030.SourcePayloads

open ColoredStorage SourcePointer

variable {α ρ : Type*}

def attach (records : List ρ) (payload : Source α (List (Option ρ))) : Source α (List (Option ρ)) :=
  payload.setRoot (records.map some ++ none :: payload.rootRecord)

def payloadRecord (records : List (Option ρ)) : List (Option ρ) :=
  (records.dropWhile Option.isSome).tail

theorem payloadRecord_attachment (records : List ρ) (payload : List (Option ρ)) :
    payloadRecord (records.map some ++ none :: payload) = payload := by
  have rest : (records.map some ++ none :: payload).dropWhile Option.isSome = none :: payload := by
    induction records <;> simp_all
  simp only [payloadRecord,rest,List.tail_cons]

theorem attachment_read (records : List ρ) (payload : Source α (List (Option ρ))) :
    decode (attach records payload).rootRecord = records ∧
      payloadRecord (attach records payload).rootRecord = payload.rootRecord := by
  cases payload with
  | leaf key old => exact ⟨decode_attachment records old,payloadRecord_attachment records old⟩
  | fork old l r => exact ⟨decode_attachment records old,payloadRecord_attachment records old⟩

theorem remove_attachment_charged (records : List ρ) (payload : Source α (List (Option ρ))) :
    Rearranges (attach records payload) payload 2 := by
  have same : (attach records payload).setRoot (payloadRecord (attach records payload).rootRecord) = payload := by
    rw [(attachment_read records payload).2]
    cases payload <;> rfl
  simpa only [same] using replace_root (attach records payload)
    (payloadRecord (attach records payload).rootRecord)

theorem add_attachment_charged (records : List ρ) (payload : Source α (List (Option ρ))) :
    Rearranges payload (attach records payload) 2 :=
  replace_root payload (records.map some ++ none :: payload.rootRecord)

theorem payload_rearranges (records : List ρ) {before after : Source α (List (Option ρ))}
    {budget : Nat} (execution : Rearranges before after budget) :
    Rearranges (attach records before) (attach records after) (budget + 4) := by
  apply (((remove_attachment_charged records before).trans execution).trans
    (add_attachment_charged records after)).mono
  omega

end ChaCha.Paper20261030.SourcePayloads
