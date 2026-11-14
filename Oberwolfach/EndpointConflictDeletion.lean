module

public import Oberwolfach.EndpointPotentialLoads

@[expose] public section

/-! Removing conflict edges from the sampled rim changes neither endpoint
potential: each counted candidate already excludes every tested conflict. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

theorem endpoint_row_predicate_conflict_deletion (P R H F:SimpleGraph V) (A B:Finset V)
    (x v:V) (p:V×V):
    EndpointRowPotentialPredicate P (R\F) H F A B x v p ↔ EndpointRowPotentialPredicate P R H F A B x v p:=by
  constructor
  · rintro ⟨hu,hel,hx,hv,hH⟩
    exact ⟨hu,hel,hx.1,hv.1,hH⟩
  · rintro ⟨hu,hel,hx,hv,hH⟩
    exact ⟨hu,hel,⟨hx,hel.2.2.2.1⟩,⟨hv,hel.2.2.2.2.2⟩,hH⟩

theorem endpoint_index_predicate_conflict_deletion (P R H F:SimpleGraph V) (A:Finset V)
    (x u:V) (e:Sym2 V):
    EndpointIndexPotentialPredicate P (R\F) H F A x u e ↔ EndpointIndexPotentialPredicate P R H F A x u e:=by
  induction e using Sym2.ind with
  | _ v w=>
    constructor
    · rintro ⟨hel,hvw,h⟩
      exact ⟨hel,hvw.1,fun a ha=>⟨(h a ha).1.1,(h a ha).2⟩⟩
    · rintro ⟨hel,hvw,h⟩
      refine ⟨hel,⟨hvw,hel.2.2.2.2.2⟩,?_⟩
      intro a ha
      have hFa:¬F.Adj x a:=by
        rcases Sym2.mem_iff.mp ha with rfl|rfl
        · exact hel.2.2.1
        · exact hel.2.2.2.1
      exact ⟨⟨(h a ha).1,hFa⟩,(h a ha).2⟩

theorem endpoint_potentials_conflict_deletion (P R H F:SimpleGraph V) (A B:Finset V)
    (x:V) (weight:Sym2 V→ℝ) (D:ℝ):
    (∀ v,endpointRowPotential P (R\F) H F A B x v weight D=endpointRowPotential P R H F A B x v weight D) ∧
    (∀ u,endpointIndexPotential P (R\F) H F A x u weight D=endpointIndexPotential P R H F A x u weight D):=by
  constructor
  · intro v
    simp only [endpointRowPotential,endpoint_row_predicate_conflict_deletion]
  · intro u
    simp only [endpointIndexPotential,endpoint_index_predicate_conflict_deletion]

end Oberwolfach
