import ChaCha.Entropy.ExpectationSwitches

/-! # Classifying the occurrence tokens by their two child intervals -/

namespace ChaCha.Entropy

open scoped BigOperators
variable {m : Nat}

def classifiedTokens (classify : Fin m → Option Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun token => (classify token).isSome)

def classifiedSide (classify : Fin m → Option Bool) (token : Fin m) : Bool :=
  (classify token).getD false

def classCount (classify : Fin m → Option Bool) (side : Bool) : Nat :=
  (Finset.univ.filter (fun token => classify token = some side)).card

theorem classification_word (sample : Equiv.Perm (Fin m)) (classify : Fin m → Option Bool) :
    ((List.finRange m).map sample).filterMap classify =
      (localOrder sample (classifiedTokens classify)).map (classifiedSide classify) := by
  unfold localOrder
  generalize (List.finRange m).map sample = word
  induction word with
  | nil => rfl
  | cons token word ih =>
    cases value : classify token with
    | none => simp [value,classifiedTokens,classifiedSide,ih]
    | some side => simp [value,classifiedTokens,classifiedSide,ih]

theorem colorCount_classified (classify : Fin m → Option Bool) (side : Bool) :
    colorCount (classifiedTokens classify) (classifiedSide classify) side = classCount classify side := by
  unfold colorCount classCount
  congr 1
  ext token
  cases value : classify token <;> simp [classifiedTokens,classifiedSide,value]

theorem classifiedTokens_card (classify : Fin m → Option Bool) :
    (classifiedTokens classify).card = classCount classify false + classCount classify true := by
  let left := Finset.univ.filter (fun token => classify token = some false)
  let right := Finset.univ.filter (fun token => classify token = some true)
  have disjoint : Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro token low high
    have low := (Finset.mem_filter.mp low).2
    have high := (Finset.mem_filter.mp high).2
    simp_all
  have union : classifiedTokens classify = left ∪ right := by
    ext token
    cases value : classify token with
    | none => simp [classifiedTokens,left,right,value]
    | some side => cases side <;> simp [classifiedTokens,left,right,value]
  rw [union,Finset.card_union_of_disjoint disjoint]
  rfl

theorem classified_switch_expectation (classify : Fin m → Option Bool) :
    uniformMean (fun sample : Equiv.Perm (Fin m) =>
      (ChaCha.alternations (((List.finRange m).map sample).filterMap classify) : ℝ)) =
      2 * (classCount classify false : ℝ) * (classCount classify true : ℝ) /
        ((classCount classify false : ℝ) + (classCount classify true : ℝ)) := by
  simp_rw [classification_word]
  rw [local_switch_expectation,colorCount_classified,colorCount_classified,classifiedTokens_card,Nat.cast_add]

theorem token_count {α : Type*} (base : List α) (keep : α → Bool) :
    (Finset.univ.filter (fun token : Fin base.length => keep (base.get token))).card =
      (base.filter keep).length := by
  let indices := (List.finRange base.length).filter (fun token => keep (base.get token))
  have nodup : indices.Nodup := (List.nodup_finRange _).filter _
  have tokens : indices.toFinset = Finset.univ.filter (fun token => keep (base.get token)) := by
    ext token
    simp [indices]
  have listed : indices.map base.get = base.filter keep := by
    have mapEq : (List.finRange base.length).map base.get = base := by
      rw [← List.ofFn_eq_map,List.ofFn_get]
    exact (List.filter_map (f := base.get) (p := keep)
      (l := List.finRange base.length)).symm.trans (congrArg (List.filter keep) mapEq)
  rw [← tokens,List.toFinset_card_of_nodup nodup,← List.length_map base.get,listed]

end ChaCha.Entropy
