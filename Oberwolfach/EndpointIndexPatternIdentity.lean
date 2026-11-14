module

public import Oberwolfach.EndpointIndexResources
public import Oberwolfach.BipartiteRelationGraph

@[expose] public section

/-! The unordered resource sum equals the actual root-spoke-omitted
potential, with the supplied parent weights and normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpoint_index_pattern_identity (P R F:SimpleGraph V) (H:V→V→Prop)
    (A B:Finset V) (x u:V) (hAB:Disjoint (insert x A) B) (hu:u∈B)
    (weight:Sym2 V→ℝ) (D:ℝ):
    (∑ e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,
      (weight e.val/D)*patternValue (endpointIndexResources x u e.val) (fun _=>true) (ordinaryResourceState R H))=
    endpointIndexPotential P R (bipartiteRelationGraph (insert x A) B hAB H) F A x u weight D:=by
  let E:=endpointEligibleGraph P F (A∩P.neighborFinset x) x
  have he (e:Sym2 V):
      e∈E.edgeFinset ∧ (e∈R.edgeSet ∧ ∀ v∈e,R.Adj x v∧H v u) ↔
      EndpointIndexPotentialPredicate P R (bipartiteRelationGraph (insert x A) B hAB H) F A x u e:=by
    constructor
    · rintro ⟨hel,hR,h⟩
      have hh:=endpoint_eligible_edge_vertices P F A x e (SimpleGraph.mem_edgeFinset.mp hel)
      refine ⟨SimpleGraph.mem_edgeFinset.mp hel,hR,?_⟩
      intro v hv
      exact ⟨(h v hv).1,(bipartiteRelationGraph_left _ _ hAB H (Finset.mem_insert_of_mem (hh v hv))).mpr ⟨hu,(h v hv).2⟩⟩
    · rintro ⟨hel,hR,h⟩
      have hh:=endpoint_eligible_edge_vertices P F A x e hel
      refine ⟨SimpleGraph.mem_edgeFinset.mpr hel,hR,?_⟩
      intro v hv
      exact ⟨(h v hv).1,((bipartiteRelationGraph_left _ _ hAB H (Finset.mem_insert_of_mem (hh v hv))).mp (h v hv).2).2⟩
  have hcoe:(∑ e:↥E.edgeFinset,(weight e.val/D)*patternValue (endpointIndexResources x u e.val) (fun _=>true) (ordinaryResourceState R H))=
      ∑ e∈E.edgeFinset,(weight e/D)*patternValue (endpointIndexResources x u e) (fun _=>true) (ordinaryResourceState R H):=by
    exact Finset.sum_coe_sort E.edgeFinset (fun e=>(weight e/D)*patternValue (endpointIndexResources x u e) (fun _=>true) (ordinaryResourceState R H))
  rw [hcoe]
  unfold endpointIndexPotential
  have hsum (f:Sym2 V→ℝ):(∑ e∈E.edgeFinset,f e)=∑ e,if e∈E.edgeFinset then f e else 0:=by
    rw [←Finset.sum_filter]
    congr 1
    ext e
    simp
  rw [hsum]
  apply Finset.sum_congr rfl
  intro e _
  rw [endpointIndexResources_value]
  have hh:=he e
  split_ifs <;> simp_all

theorem endpoint_index_pattern_mean (P F:SimpleGraph V) (A:Finset V) (B:Finset V) (x:V)
    (weight:Sym2 V→ℝ) (pR pH:ℝ) (hpR:0<pR) (hpH:0<pH) (hB:0<B.card):
    pR^3*pH^2*(∑ e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,
      weight e.val/(B.card*pR^2*pH^3))=
      pR/(B.card*pH)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e):=by
  have hs:(∑ e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,
      weight e.val/(B.card*pR^2*pH^3))=
      ∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e/(B.card*pR^2*pH^3):=by
    exact Finset.sum_coe_sort _ (fun e=>weight e/(B.card*pR^2*pH^3))
  rw [hs,←Finset.sum_div]
  have hb:(0:ℝ)<B.card:=Nat.cast_pos.mpr hB
  field_simp <;> ring

end Oberwolfach
