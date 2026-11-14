module

public import Oberwolfach.EndpointRowResources
public import Oberwolfach.EndpointPotentialLoads
public import Oberwolfach.BipartiteRelationGraph

@[expose] public section

/-! The resource-pattern expression is exactly the manuscript's row
potential with its original eligible graph, coefficient and normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpointRowResources_value {U:Type} [Fintype U] [DecidableEq U]
    (R:SimpleGraph V) (H:V→U→Prop) (x v w:V) (u:U):
    patternValue (endpointRowResources x v w u) (fun _=>true) (ordinaryResourceState R H)=
      if R.Adj x w∧R.Adj v w∧H x u∧H v u∧H w u then (1:ℝ) else 0:=by
  rw [patternValue_indicator]
  congr 1
  apply propext
  simp only [endpointRowResources,Finset.forall_mem_union,Finset.forall_mem_image,
    Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq,
    ordinaryResourceState,Sum.elim_inl,Sum.elim_inr,decide_eq_true_eq,SimpleGraph.mem_edgeSet]
  tauto

theorem endpoint_row_pattern_identity (P R F:SimpleGraph V) (H:V→V→Prop)
    (A B:Finset V) (x v:V) (hAB:Disjoint (insert x A) B) (hv:v∈A)
    (weight:Sym2 V→ℝ) (D:ℝ):
    (∑ p:EndpointRowCandidates (endpointEligibleGraph P F (A∩P.neighborFinset x) x) A B v,
      (weight s(v,p.val.2)/D)*patternValue (endpointRowResources x v p.val.2 p.val.1)
        (fun _=>true) (ordinaryResourceState R H))=
    endpointRowPotential P R (bipartiteRelationGraph (insert x A) B hAB H) F A B x v weight D:=by
  let E:=endpointEligibleGraph P F (A∩P.neighborFinset x) x
  have he (p:V×V):
      (p.1∈B∧p.2∈A∧E.Adj v p.2)∧(R.Adj x p.2∧R.Adj v p.2∧H x p.1∧H v p.1∧H p.2 p.1) ↔
      EndpointRowPotentialPredicate P R (bipartiteRelationGraph (insert x A) B hAB H) F A B x v p:=by
    constructor
    · rintro ⟨⟨hu,hw,he⟩,hR1,hR2,hx,hvH,hwH⟩
      exact ⟨hu,he,hR1,hR2,
        (bipartiteRelationGraph_left _ _ hAB H (Finset.mem_insert_self _ _)).mpr ⟨hu,hx⟩,
        (bipartiteRelationGraph_left _ _ hAB H (Finset.mem_insert_of_mem hv)).mpr ⟨hu,hvH⟩,
        (bipartiteRelationGraph_left _ _ hAB H (Finset.mem_insert_of_mem hw)).mpr ⟨hu,hwH⟩⟩
    · rintro ⟨hu,hel,hR1,hR2,hx,hvH,hwH⟩
      have hw:p.2∈A:=(Finset.mem_inter.mp hel.2.1).1
      exact ⟨⟨hu,hw,hel⟩,hR1,hR2,
        ((bipartiteRelationGraph_left _ _ hAB H (Finset.mem_insert_self _ _)).mp hx).2,
        ((bipartiteRelationGraph_left _ _ hAB H (Finset.mem_insert_of_mem hv)).mp hvH).2,
        ((bipartiteRelationGraph_left _ _ hAB H (Finset.mem_insert_of_mem hw)).mp hwH).2⟩
  have hs:(∑ p:V×V,if p.1∈B∧p.2∈A∧E.Adj v p.2 then
      (weight s(v,p.2)/D)*patternValue (endpointRowResources x v p.2 p.1) (fun _=>true) (ordinaryResourceState R H) else 0)=
      ∑ p:EndpointRowCandidates E A B v,(weight s(v,p.val.2)/D)*patternValue
        (endpointRowResources x v p.val.2 p.val.1) (fun _=>true) (ordinaryResourceState R H):=by
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype _ (fun _=>by simp) _
  rw [←hs]
  unfold endpointRowPotential
  apply Finset.sum_congr rfl
  intro p _
  rw [endpointRowResources_value]
  have hh:=he p
  split_ifs <;> simp_all

end Oberwolfach
