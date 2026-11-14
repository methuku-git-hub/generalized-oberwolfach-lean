module

public import Oberwolfach.FinitePredicateLoss
public import Oberwolfach.EndpointPotentialLoads
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Endpoint index potentials under realised deletions. The root spoke is
omitted, and the parent edge weights and their normalization stay fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

theorem endpoint_index_predicate_sdiff (P R H F D E:SimpleGraph V) (A:Finset V)
    (x u:V) (e:Sym2 V) :
    EndpointIndexPotentialPredicate P (R\D) (H\E) F A x u e ↔
      EndpointIndexPotentialPredicate P R H F A x u e ∧
      e∉D.edgeSet ∧ ∀ v∈e,¬D.Adj x v∧¬E.Adj v u := by
  induction e using Sym2.ind with
  | _ v w =>
    simp only [EndpointIndexPotentialPredicate,SimpleGraph.mem_edgeSet,SimpleGraph.sdiff_adj]
    constructor
    · rintro ⟨hel,⟨hR,hnD⟩,hall⟩
      exact ⟨⟨hel,hR,fun z hz=>⟨(hall z hz).1.1,(hall z hz).2.1⟩⟩,hnD,
        fun z hz=>⟨(hall z hz).1.2,(hall z hz).2.2⟩⟩
    · rintro ⟨⟨hel,hR,hall⟩,hnD,hno⟩
      exact ⟨hel,⟨hR,hnD⟩,fun z hz=>⟨⟨(hall z hz).1,(hno z hz).1⟩,⟨(hall z hz).2,(hno z hz).2⟩⟩⟩

theorem endpoint_eligible_edge_vertices (P F:SimpleGraph V) (A:Finset V) (x:V)
    (e:Sym2 V) (he:e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet) :
    ∀ v∈e,v∈A := by
  induction e using Sym2.ind with
  | _ v w =>
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl|rfl
    · exact (Finset.mem_inter.mp he.1).1
    · exact (Finset.mem_inter.mp he.2.1).1

theorem internal_graph_edge_count (D:SimpleGraph V) (A:Finset V) (L:ℝ)
    (hD:∀ v∈A,(D.degree v:ℝ)≤L) :
    (((spanningRestriction D A).edgeFinset).card:ℝ)≤A.card*L := by
  have hsub:(spanningRestriction D A).edgeFinset⊆A.biUnion (fun v=>D.incidenceFinset v):=by
    intro e he
    induction e using Sym2.ind with
    | _ v w =>
      have hh:=(spanningRestriction_adj D A v w).mp (SimpleGraph.mem_edgeFinset.mp he)
      exact Finset.mem_biUnion.mpr ⟨v,hh.2.1,SimpleGraph.mem_incidenceFinset.mpr ⟨hh.1,by simp⟩⟩
  calc
    _ ≤ ((A.biUnion (fun v=>D.incidenceFinset v)).card:ℝ):=Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ v∈A,((D.incidenceFinset v).card:ℝ):=by exact_mod_cast Finset.card_biUnion_le
    _ = ∑ v∈A,(D.degree v:ℝ):=by simp only [SimpleGraph.card_incidenceFinset_eq_degree]
    _ ≤ ∑ v∈A,L:=Finset.sum_le_sum hD
    _ = _:=by simp

theorem endpoint_index_removed_count (P R H F D E:SimpleGraph V) (A:Finset V)
    (x u:V) (L:ℝ) (hD:∀ v∈A,(D.degree v:ℝ)≤L) :
    ((Finset.univ.filter (fun e:Sym2 V=>EndpointIndexPotentialPredicate P R H F A x u e ∧
      ¬EndpointIndexPotentialPredicate P (R\D) (H\E) F A x u e)).card:ℝ)≤
      A.card*(L+(D.degree x:ℝ)+E.degree u) := by
  let Z:=D.neighborFinset x∪E.neighborFinset u
  let J:=(Z.product A).image (fun p:V×V=>s(p.1,p.2))
  have hsub:Finset.univ.filter (fun e:Sym2 V=>EndpointIndexPotentialPredicate P R H F A x u e ∧
      ¬EndpointIndexPotentialPredicate P (R\D) (H\E) F A x u e)⊆(spanningRestriction D A).edgeFinset∪J:=by
    intro e he
    obtain ⟨hp,hno⟩:=(Finset.mem_filter.mp he).2
    have hvertices:=endpoint_eligible_edge_vertices P F A x e hp.1
    by_cases hDe:e∈D.edgeSet
    · apply Finset.mem_union_left
      induction e using Sym2.ind with
      | _ v w =>
        exact SimpleGraph.mem_edgeFinset.mpr ((spanningRestriction_adj D A v w).mpr
          ⟨hDe,hvertices v (by simp),hvertices w (by simp)⟩)
    · have hz:∃ v∈e,D.Adj x v∨E.Adj v u:=by
        by_contra hn
        have hn':∀ v∈e,¬D.Adj x v∧¬E.Adj v u:=by simpa only [not_exists,not_and,not_or] using hn
        exact hno ((endpoint_index_predicate_sdiff P R H F D E A x u e).mpr ⟨hp,hDe,hn'⟩)
      obtain ⟨v,hve,hv⟩:=hz
      obtain ⟨w,heq⟩:=Sym2.mem_iff_exists.mp hve
      have hw:w∈A:=hvertices w (by rw [heq];simp)
      have hvZ:v∈Z:=by
        rcases hv with hv|hv
        · exact Finset.mem_union_left _ (by simpa using hv)
        · exact Finset.mem_union_right _ (by simpa using hv.symm)
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v,w),Finset.mem_product.mpr ⟨hvZ,hw⟩,heq.symm⟩)
  have hJ:(J.card:ℝ)≤((D.degree x:ℝ)+E.degree u)*A.card:=by
    have hc:J.card≤Z.card*A.card:=Finset.card_image_le.trans_eq (Finset.card_product _ _)
    have hz:Z.card≤D.degree x+E.degree u:=by
      simpa only [Z,SimpleGraph.card_neighborFinset_eq_degree] using
        Finset.card_union_le (D.neighborFinset x) (E.neighborFinset u)
    exact (Nat.cast_le.mpr hc).trans (by exact_mod_cast Nat.mul_le_mul_right A.card hz)
  have hc:((Finset.univ.filter (fun e:Sym2 V=>EndpointIndexPotentialPredicate P R H F A x u e ∧
      ¬EndpointIndexPotentialPredicate P (R\D) (H\E) F A x u e)).card:ℝ)≤
      ((spanningRestriction D A).edgeFinset.card:ℝ)+J.card:=by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hInt:=internal_graph_edge_count D A L hD
  nlinarith only [hc,hJ,hInt]

theorem endpoint_index_potential_deletion (P R H F D E:SimpleGraph V) (A:Finset V)
    (x u:V) (weight:Sym2 V→ℝ) (d M L:ℝ) (hM:0≤M)
    (hw:∀ e,e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet →
      0≤weight e/d∧weight e/d≤M) (hD:∀ v∈A,(D.degree v:ℝ)≤L) :
    0≤endpointIndexPotential P R H F A x u weight d-endpointIndexPotential P (R\D) (H\E) F A x u weight d ∧
    |endpointIndexPotential P (R\D) (H\E) F A x u weight d-endpointIndexPotential P R H F A x u weight d|≤
      M*A.card*(L+(D.degree x:ℝ)+E.degree u) := by
  have hh:=finite_predicate_loss (EndpointIndexPotentialPredicate P R H F A x u)
    (EndpointIndexPotentialPredicate P (R\D) (H\E) F A x u) (fun e=>weight e/d) M
    (fun e he=>((endpoint_index_predicate_sdiff P R H F D E A x u e).mp he).1)
    (fun e he=>hw e he.1)
  change 0≤endpointIndexPotential P R H F A x u weight d-endpointIndexPotential P (R\D) (H\E) F A x u weight d ∧ _ at hh
  refine ⟨hh.1,?_⟩
  rw [abs_sub_comm,abs_of_nonneg hh.1]
  have hb:=hh.2.trans (mul_le_mul_of_nonneg_left (endpoint_index_removed_count P R H F D E A x u L hD) hM)
  simpa only [endpointIndexPotential,mul_assoc] using hb

end Oberwolfach
