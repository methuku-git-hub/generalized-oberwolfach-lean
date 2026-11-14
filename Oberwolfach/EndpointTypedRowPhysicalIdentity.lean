module

public import Oberwolfach.OrdinaryEndpointEligibleGeometry
public import Oberwolfach.EndpointRowPatternIdentity

@[expose] public section
/-! The two-domain row pattern is exactly the endpoint potential on the
physical sum; coefficients are the same fixed physical parent weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem endpoint_typed_row_physical_identity (P R F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (B:Finset U) (x v:V) (weight:Sym2 (V⊕U)→ℝ) (D:ℝ):
    (∑ p:EndpointRowCandidates (endpointEligibleGraph P F (A∩P.neighborFinset x) x) A B v,
      (weight s(Sum.inl v,Sum.inl p.val.2)/D)*
        patternValue (endpointRowResources x v p.val.2 p.val.1) (fun _=>true) (ordinaryResourceState R H))=
    endpointRowPotential (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph R (fun _ _=>False)) (ordinaryPhysicalGraph ⊥ H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (A.image Sum.inl) (B.image Sum.inr)
      (Sum.inl x) (Sum.inl v) weight D:=by
  let E:=endpointEligibleGraph P F (A∩P.neighborFinset x) x
  have hs:(∑ p:U×V,if p.1∈B∧p.2∈A∧E.Adj v p.2 then
      (weight s(Sum.inl v,Sum.inl p.2)/D)*patternValue (endpointRowResources x v p.2 p.1)
        (fun _=>true) (ordinaryResourceState R H) else 0)=
      ∑ p:EndpointRowCandidates E A B v,(weight s(Sum.inl v,Sum.inl p.val.2)/D)*
        patternValue (endpointRowResources x v p.val.2 p.val.1) (fun _=>true) (ordinaryResourceState R H):=by
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype _ (fun _=>by simp) _
  rw [←hs,Fintype.sum_prod_type]
  simp_rw [endpointRowResources_value]
  unfold endpointRowPotential EndpointRowPotentialPredicate
  rw [ordinary_endpoint_eligible_graph]
  simp only [Fintype.sum_prod_type,Fintype.sum_sum_type]
  simp only [ordinaryPhysicalGraph,Finset.mem_image,Sum.inl.injEq,Sum.inr.injEq,
    Sum.inl_ne_inr,Sum.inr_ne_inl,exists_false,exists_eq_right,Finset.sum_const_zero,zero_add,add_zero]
  simp only [and_false, false_and, exists_false, not_false_eq_true, ↓reduceIte,
    Finset.sum_const_zero, zero_add, add_zero]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro w _
  have hw:E.Adj v w→w∈A:=fun h=>(Finset.mem_inter.mp h.2.1).1
  dsimp [E] at *
  split_ifs <;> simp_all
end Oberwolfach
