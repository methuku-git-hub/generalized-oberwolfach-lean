module

public import Oberwolfach.EndpointPotentialLoads
public import Oberwolfach.BipartiteRelationGraph

@[expose] public section

/-! Endpoint potentials use only spokes between the fixed rim/root domain
and B. Restricting a larger spoke graph to that domain leaves them unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpoint_potentials_spoke_congr (P R H H' F:SimpleGraph V) (A B:Finset V)
    (x:V) (weight:Sym2 V→ℝ) (D:ℝ)
    (h:∀ a∈insert x A,∀ u∈B,H.Adj a u↔H'.Adj a u):
    (∀ v,endpointRowPotential P R H F A B x v weight D=endpointRowPotential P R H' F A B x v weight D) ∧
    (∀ u∈B,endpointIndexPotential P R H F A x u weight D=endpointIndexPotential P R H' F A x u weight D):=by
  constructor
  · intro v
    unfold endpointRowPotential
    apply Finset.sum_congr rfl
    intro p _
    have he:EndpointRowPotentialPredicate P R H F A B x v p↔EndpointRowPotentialPredicate P R H' F A B x v p:=by
      by_cases hu:p.1∈B
      · by_cases hvw:(endpointEligibleGraph P F (A∩P.neighborFinset x) x).Adj v p.2
        · have hv:v∈A:=(Finset.mem_inter.mp hvw.1).1
          have hw:p.2∈A:=(Finset.mem_inter.mp hvw.2.1).1
          simp only [EndpointRowPotentialPredicate,hu,hvw,true_and,
            h x (Finset.mem_insert_self _ _) p.1 hu,
            h v (Finset.mem_insert_of_mem hv) p.1 hu,
            h p.2 (Finset.mem_insert_of_mem hw) p.1 hu]
        · simp [EndpointRowPotentialPredicate,hvw]
      · simp [EndpointRowPotentialPredicate,hu]
    rw [he]
  · intro u hu
    unfold endpointIndexPotential
    apply Finset.sum_congr rfl
    intro e _
    have he:EndpointIndexPotentialPredicate P R H F A x u e↔EndpointIndexPotentialPredicate P R H' F A x u e:=by
      by_cases hel:e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet
      · have hv:∀ v∈e,v∈A:=by
          induction e using Sym2.ind with
          | _ v w=>
            intro a ha
            rcases Sym2.mem_iff.mp ha with rfl|rfl
            · exact (Finset.mem_inter.mp hel.1).1
            · exact (Finset.mem_inter.mp hel.2.1).1
        simp only [EndpointIndexPotentialPredicate,hel,true_and]
        apply and_congr_right
        intro _
        apply forall_congr'
        intro v
        apply forall_congr'
        intro he
        rw [h v (Finset.mem_insert_of_mem (hv v he)) u hu]
      · simp [EndpointIndexPotentialPredicate,hel]
    rw [he]

theorem endpoint_potentials_on_larger_spoke_domain (P R F:SimpleGraph V) (H:V→V→Prop)
    (A B Y:Finset V) (x:V) (hA:A⊆Y) (hx:x∈Y) (hYB:Disjoint Y B)
    (weight:Sym2 V→ℝ) (D:ℝ):
    let hAB:Disjoint (insert x A) B:=hYB.mono_left (Finset.insert_subset hx hA)
    (∀ v,endpointRowPotential P R (bipartiteRelationGraph Y B hYB H) F A B x v weight D=
      endpointRowPotential P R (bipartiteRelationGraph (insert x A) B hAB H) F A B x v weight D) ∧
    (∀ u∈B,endpointIndexPotential P R (bipartiteRelationGraph Y B hYB H) F A x u weight D=
      endpointIndexPotential P R (bipartiteRelationGraph (insert x A) B hAB H) F A x u weight D):=by
  dsimp only
  apply endpoint_potentials_spoke_congr
  intro a ha u hu
  have haY:a∈Y:=Finset.insert_subset hx hA ha
  rw [bipartiteRelationGraph_left _ _ hYB H haY,
    bipartiteRelationGraph_left _ _ (hYB.mono_left (Finset.insert_subset hx hA)) H ha]

end Oberwolfach
