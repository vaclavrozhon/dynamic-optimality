import ChaCha.Paper20261030.AccessSequence
import ChaCha.Demands
import Mathlib.Data.List.Chain

/-!
# Ordered point words and chronological adjacency

A chronological word lists actual points in strictly increasing timestamp
order. Its finite set is therefore an input instance, and neighboring
letters are precisely chronological neighbors. Projection of keys and
filtering preserve the strict timestamp order.
-/

namespace ChaCha.Paper20261030.Rectangles

def Chronological (ps : List Point) : Prop := ps.Pairwise (fun p q => p.2 < q.2)

theorem chronological_instance {ps : List Point} (hs : Chronological ps) : Instance ps.toFinset := by
  induction ps with
  | nil => intro p hp; simp at hp
  | cons p ps ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    have hi := ih htail
    intro q hq r hr he
    simp only [List.mem_toFinset,List.mem_cons] at hq hr
    rcases hq with rfl | hq <;> rcases hr with rfl | hr
    · rfl
    · have := hhead r hr; omega
    · have := hhead q hq; omega
    · exact hi q (List.mem_toFinset.mpr hq) r (List.mem_toFinset.mpr hr) he

theorem chronological_nodup {ps : List Point} (hs : Chronological ps) : ps.Nodup := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    apply List.nodup_cons.mpr
    refine ⟨?_,ih htail⟩
    intro hp
    have := hhead p hp
    omega

theorem chronological_project {ps : List Point} (hs : Chronological ps) (f : Int → Int) :
    Chronological (ps.map (mapPoint f)) :=
  hs.map _ (fun _ _ h => h)

theorem chronological_filter {ps : List Point} (hs : Chronological ps) (keep : Point → Bool) :
    Chronological (ps.filter keep) := hs.filter keep

theorem chronological_first {p : Point} {ps : List Point} (hs : Chronological (p :: ps)) :
    ∀ q ∈ (p :: ps).toFinset, p.2 ≤ q.2 := by
  intro q hq
  rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with rfl | hq
  · exact le_rfl
  · exact ((List.pairwise_cons.mp hs).1 q hq).le

theorem chronological_head_next {p q : Point} {ps : List Point}
    (hs : Chronological (p :: q :: ps)) : Next (p :: q :: ps).toFinset p q := by
  obtain ⟨hp,ht⟩ := List.pairwise_cons.mp hs
  obtain ⟨hq,_⟩ := List.pairwise_cons.mp ht
  refine ⟨by simp,by simp,hp q (by simp),?_⟩
  intro z hz hpz hzq
  simp only [List.mem_toFinset,List.mem_cons] at hz
  rcases hz with rfl | rfl | hz
  · omega
  · omega
  · have := hq z hz; omega

theorem chronological_next_prepend {a : Point} {ps : List Point}
    (hs : Chronological (a :: ps)) {p q : Point} (hn : Next ps.toFinset p q) :
    Next (a :: ps).toFinset p q := by
  refine ⟨by simp [List.mem_toFinset.mp hn.1],by simp [List.mem_toFinset.mp hn.2.1],hn.2.2.1,?_⟩
  intro z hz hpz hzq
  rcases List.mem_cons.mp (List.mem_toFinset.mp hz) with rfl | hz
  · have := (List.pairwise_cons.mp hs).1 p (List.mem_toFinset.mp hn.1)
    omega
  · exact hn.2.2.2 z (List.mem_toFinset.mpr hz) hpz hzq

theorem chronological_chain {ps : List Point} (hs : Chronological ps) :
    ps.IsChain (Next ps.toFinset) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have ht := (List.pairwise_cons.mp hs).2
    have htail := (ih ht).imp (fun _ _ h => chronological_next_prepend hs h)
    cases ps with
    | nil => simp
    | cons q ps =>
      exact List.isChain_cons_cons.mpr ⟨chronological_head_next hs,htail⟩

theorem downUpAt_iff_previous {P : Finset Point} (hP : Instance P) (f : Int → Int)
    {p q : Point} (hn : Next P p q) :
    DownUpAt P f q ↔ ActiveDown P f p ∧ ¬ ActiveDown P f q := by
  constructor
  · rintro ⟨r,hr,hstate⟩
    have he := next_previous_unique hP hr hn
    exact he ▸ hstate
  · exact fun h => ⟨p,hn,h⟩

end ChaCha.Paper20261030.Rectangles
