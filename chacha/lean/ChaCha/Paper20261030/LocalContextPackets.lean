import ChaCha.Paper20261030.LocalPacketRead
import ChaCha.Paper20261030.LocalDecoratedReassembly
import ChaCha.Paper20261030.SourceRecordMap

/-! Acquisition of the exposed connector packets by actual local reads.
The runtime blueprint stores only prefix lengths and block-presence bits.
Suppressed connectors share a reached root; their successive prefixes
are read at successive scalar offsets. A present block is never entered.
-/

namespace ChaCha.Paper20261030.OrderedContext.PacketAcquisition

open RouterProjection ColoredStorage SourcePointer ProjectionLocal PacketReadController
open Local (present)

variable {ι α ρ : Type*}

def commands (bits : ι → Bool) (offset : Nat) : Source ι Nat → List Command
  | .leaf key count => if bits key then [.sample offset count] else []
  | .fork count l r =>
      match present bits l.shape,present bits r.shape with
      | false,false => []
      | true,false => .sample offset count::commands bits (offset+count) l
      | false,true => .sample offset count::commands bits (offset+count) r
      | true,true => [.sample offset count] ++
          (PacketReadController.left (commands bits 0 l) ++ PacketReadController.right (commands bits 0 r))

def packets (bits : ι → Bool) : Source ι (List ρ) → List (List ρ)
  | .leaf key records => if bits key then [records] else []
  | .fork records l r => if present bits l.shape || present bits r.shape then
      records::(packets bits l++packets bits r) else []

theorem packets_absent (bits : ι → Bool) (t : Source ι (List ρ))
    (absent : present bits t.shape = false) : packets bits t = [] := by
  cases t with
  | leaf key records => change bits key = false at absent; simp [packets,absent]
  | fork records l r => simp only [Source.shape,present] at absent; simp [packets,absent]

theorem root_set (source : Source α (List ρ)) (records : List ρ) :
    (source.setRoot records).rootRecord = records := by cases source <;> rfl

theorem set_set (source : Source α (List ρ)) (first last : List ρ) :
    (source.setRoot first).setRoot last = source.setRoot last := by cases source <;> rfl

theorem decorate_nil (source : Projected α ρ) : decorate [] source = source := by
  cases source with
  | none => rfl
  | some source => cases source <;> rfl

theorem decorate_append (xs ys : List ρ) (source : Projected α ρ) :
    decorate xs (decorate ys source) = decorate (xs++ys) source := by
  cases source with
  | none => rfl
  | some source => cases source <;> simp [decorate,Source.rootRecord,Source.setRoot,List.append_assoc]

theorem root_sample (extras records : List ρ) (source : Source α (List ρ)) :
    Collects [.sample extras.length records.length]
      (source.setRoot (extras++records++source.rootRecord)) [records] := by
  have read := sample (source.setRoot (extras++records++source.rootRecord)) extras.length records.length
  have root : (source.setRoot (extras++records++source.rootRecord)).rootRecord =
      extras++records++source.rootRecord := by cases source <;> rfl
  rw [root] at read
  simpa only [List.append_assoc,List.drop_left,List.take_left] using read

theorem acquire (blocks : ι → Projected α ρ) (t : Source ι (List ρ)) (extras : List ρ) :
    ProjectedCollects (commands (fun key => (blocks key).isSome) extras.length (t.mapRecords List.length))
      (decorate extras (decorated blocks t)) (packets (fun key => (blocks key).isSome) t) := by
  let bits := fun key => (blocks key).isSome
  change ProjectedCollects (commands bits extras.length (t.mapRecords List.length))
    (decorate extras (decorated blocks t)) (packets bits t)
  induction t generalizing extras with
  | leaf key records =>
    cases hb : blocks key with
    | none => simp [commands,packets,Source.mapRecords,decorated,decorate,hb,bits,ProjectedCollects]
    | some block =>
      have actual := root_sample extras records block
      simpa only [commands,packets,Source.mapRecords,decorated,decorate_append,decorate,
        hb,bits,Option.isSome_some,if_true,Option.map_some,ProjectedCollects,
        root_set,set_set,List.append_assoc] using actual
  | fork records l r ihl ihr =>
    have pl := Local.decorated_present blocks l
    have pr := Local.decorated_present blocks r
    change (decorated blocks l).isSome = present bits l.shape at pl
    change (decorated blocks r).isSome = present bits r.shape at pr
    cases hl : decorated blocks l with
    | none =>
      have bl : present bits l.shape = false := pl.symm.trans (congrArg Option.isSome hl)
      have emptyL := packets_absent bits l bl
      cases hr : decorated blocks r with
      | none =>
        have br : present bits r.shape = false := pr.symm.trans (congrArg Option.isSome hr)
        simp only [decorated,hl,hr,join,decorate,Option.map_none,ProjectedCollects,packets,bl,br,Bool.false_or,Bool.false_eq_true,if_false]
      | some rightTree =>
        have br : present bits r.shape = true := pr.symm.trans (congrArg Option.isSome hr)
        have tail := ihr (extras++records)
        rw [hr] at tail
        have actual := (root_sample extras records rightTree).trans tail
        simpa only [commands,Source.mapRecords,Source.mapRecords_shape,decorated,hl,hr,join,
          decorate_append,decorate,Option.map_some,ProjectedCollects,packets,bl,br,Bool.false_or,
          if_true,emptyL,List.nil_append,List.length_append,List.singleton_append,
          root_set,set_set,List.append_assoc] using actual
    | some leftTree =>
      have bl : present bits l.shape = true := pl.symm.trans (congrArg Option.isSome hl)
      cases hr : decorated blocks r with
      | none =>
        have br : present bits r.shape = false := pr.symm.trans (congrArg Option.isSome hr)
        have emptyR := packets_absent bits r br
        have tail := ihl (extras++records)
        rw [hl] at tail
        have actual := (root_sample extras records leftTree).trans tail
        simpa only [commands,Source.mapRecords,Source.mapRecords_shape,decorated,hl,hr,join,
          decorate_append,decorate,Option.map_some,ProjectedCollects,packets,bl,br,Bool.true_or,
          if_true,emptyR,List.append_nil,List.length_append,List.singleton_append,
          root_set,set_set,List.append_assoc] using actual
      | some rightTree =>
        have br : present bits r.shape = true := pr.symm.trans (congrArg Option.isSome hr)
        have leftRun := ihl []
        have rightRun := ihr []
        rw [decorate_nil,hl] at leftRun
        rw [decorate_nil,hr] at rightRun
        have children := (leftRun.left (records := extras++records)).trans rightRun.right
        have first := root_sample extras records (.fork [] leftTree rightTree)
        simp only [Source.rootRecord,Source.setRoot,List.append_nil] at first
        have actual := first.trans children
        simpa only [commands,Source.mapRecords,Source.mapRecords_shape,decorated,hl,hr,join,
          decorate_append,decorate,Option.map_some,ProjectedCollects,packets,bl,br,Bool.true_or,
          if_true,List.length_nil,List.singleton_append,Source.setRoot,Source.rootRecord,List.append_nil] using actual

end ChaCha.Paper20261030.OrderedContext.PacketAcquisition
