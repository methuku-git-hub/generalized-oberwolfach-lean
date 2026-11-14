module

public import Oberwolfach.Neighbourhoods
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! Explicit common-neighbour lower bounds and the exact forbidden set
removed when extending a bounded conflict-free labelled configuration. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem common_neighbour_card_lower {V I : Type*} [DecidableEq V]
    (A : Finset V) (J : Finset I) (N : I → Finset V) (δ : ℝ)
    (hdeg : ∀ j∈J,δ*(A.card:ℝ)≤((A∩N j).card:ℝ)) :
    (1-(J.card:ℝ)*(1-δ))*(A.card:ℝ)≤((common A J N).card:ℝ) := by
  let D := J.biUnion (fun j=>A\N j)
  have he : common A J N=A\D := by
    ext x
    simp only [common,D,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_biUnion]
    constructor
    · rintro ⟨ha,hall⟩
      exact ⟨ha,by rintro ⟨j,hj,_,hn⟩;exact hn (hall j hj)⟩
    · rintro ⟨ha,hnot⟩
      refine ⟨ha,?_⟩
      intro j hj
      by_contra hn
      exact hnot ⟨j,hj,ha,hn⟩
  have hdeficit (j : I) (hj : j∈J) : ((A\N j).card:ℝ)≤(1-δ)*(A.card:ℝ) := by
    have hh : ((A\N j).card:ℝ)+(A∩N j).card=A.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter A (N j)
    nlinarith only [hh,hdeg j hj]
  have hD : (D.card:ℝ)≤(J.card:ℝ)*((1-δ)*(A.card:ℝ)) := by
    calc
      _ ≤ ∑ j∈J,((A\N j).card:ℝ) := by exact_mod_cast (Finset.card_biUnion_le : D.card≤_)
      _ ≤ ∑ _j∈J,(1-δ)*(A.card:ℝ) := Finset.sum_le_sum hdeficit
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  have hc : (A.card:ℝ)≤(A\D).card+D.card := by exact_mod_cast (Finset.card_le_card_sdiff_add_card (s:=A) (t:=D))
  rw [he]
  nlinarith only [hc,hD]


theorem forbidden_used_neighbours_card {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) (L : ℝ) (hF : ∀ v,(F.degree v:ℝ)≤L) :
    ((S∪S.biUnion (fun v=>F.neighborFinset v)).card:ℝ)≤(S.card:ℝ)*(L+1) := by
  have hu : ((S∪S.biUnion (fun v=>F.neighborFinset v)).card:ℝ)≤S.card+(S.biUnion (fun v=>F.neighborFinset v)).card := by
    exact_mod_cast Finset.card_union_le S (S.biUnion (fun v=>F.neighborFinset v))
  have hb : ((S.biUnion (fun v=>F.neighborFinset v)).card:ℝ)≤(S.card:ℝ)*L := by
    calc
      _ ≤ ∑ v∈S,((F.neighborFinset v).card:ℝ) := by exact_mod_cast (Finset.card_biUnion_le : (S.biUnion (fun v=>F.neighborFinset v)).card≤_)
      _ ≤ ∑ _v∈S,L := Finset.sum_le_sum (fun v _=>by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hF v)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  nlinarith only [hu,hb]


theorem dense_common_neighbour_avoiding_used {V : Type*} [Fintype V] [DecidableEq V]
    (P F : SimpleGraph V) (A R S : Finset V) (δ L : ℝ)
    (hdeg : ∀ v∈R,δ*(A.card:ℝ)≤((A∩P.neighborFinset v).card:ℝ))
    (hF : ∀ v,(F.degree v:ℝ)≤L) :
    (1-(R.card:ℝ)*(1-δ))*(A.card:ℝ)-(S.card:ℝ)*(L+1)≤
      ((common A R (fun v=>P.neighborFinset v)\(S∪S.biUnion (fun v=>F.neighborFinset v))).card:ℝ) := by
  have hh := common_neighbour_card_lower A R (fun v=>P.neighborFinset v) δ hdeg
  have hb := forbidden_used_neighbours_card F S L hF
  have hc : ((common A R (fun v=>P.neighborFinset v)).card:ℝ)≤
      (common A R (fun v=>P.neighborFinset v)\(S∪S.biUnion (fun v=>F.neighborFinset v))).card+
      (S∪S.biUnion (fun v=>F.neighborFinset v)).card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s:=common A R (fun v=>P.neighborFinset v)) (t:=S∪S.biUnion (fun v=>F.neighborFinset v)))
  linarith only [hh,hb,hc]

end Oberwolfach
