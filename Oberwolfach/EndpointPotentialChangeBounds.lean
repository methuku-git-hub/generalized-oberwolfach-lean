module

public import Oberwolfach.EndpointPotentialDeletionBounds

@[expose] public section
/-! Two bounded graph edits, including additions, change endpoint potentials
by at most the sum of their two deletion bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem graph_union_delete_other_difference (R Q:SimpleGraph V):
    (R⊔Q)\(Q\R)=R:=by
  ext v w
  simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj]
  tauto

theorem endpoint_potential_change_bounds (P R H F Q J:SimpleGraph V) (A B:Finset V)
    (x:V) (weight:Sym2 V→ℝ) (d C L:ℝ) (hA:0<A.card) (hBA:B.card≤A.card)
    (hC:0≤C) (hL:0≤L)
    (hw:∀e,e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet→
      0≤weight e/d ∧ weight e/d≤C/(A.card:ℝ)^2)
    (hRQ:∀v,((R\Q).degree v:ℝ)≤L) (hQR:∀v,((Q\R).degree v:ℝ)≤L)
    (hHJ:∀v,((H\J).degree v:ℝ)≤L) (hJH:∀v,((J\H).degree v:ℝ)≤L):
    (∀v,|endpointRowPotential P Q J F A B x v weight d-
      endpointRowPotential P R H F A B x v weight d|≤10*C*L/A.card) ∧
    (∀u,|endpointIndexPotential P Q J F A x u weight d-
      endpointIndexPotential P R H F A x u weight d|≤6*C*L/A.card):=by
  have hR:=endpoint_potential_deletion_bounds P (R⊔Q) (H⊔J) F (Q\R) (J\H) A B x weight d C L hA hBA hC hL hw
    (by intro v;convert hQR v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hJH v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _)
  have hQ:=endpoint_potential_deletion_bounds P (R⊔Q) (H⊔J) F (R\Q) (H\J) A B x weight d C L hA hBA hC hL hw
    (by intro v;convert hRQ v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hHJ v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _)
  rw [graph_union_delete_other_difference R Q,graph_union_delete_other_difference H J] at hR
  have heR:(R⊔Q)\(R\Q)=Q:=by rw [sup_comm,graph_union_delete_other_difference]
  have heH:(H⊔J)\(H\J)=J:=by rw [sup_comm,graph_union_delete_other_difference]
  rw [heR,heH] at hQ
  constructor
  · intro v
    have ht:=abs_sub_le (endpointRowPotential P Q J F A B x v weight d)
      (endpointRowPotential P (R⊔Q) (H⊔J) F A B x v weight d)
      (endpointRowPotential P R H F A B x v weight d)
    have hh:=hR.1 v
    rw [abs_sub_comm] at hh
    have hn:5*C*L/A.card+5*C*L/A.card=10*C*L/A.card:=by ring
    linarith only [ht,hh,hQ.1 v,hn]
  · intro u
    have ht:=abs_sub_le (endpointIndexPotential P Q J F A x u weight d)
      (endpointIndexPotential P (R⊔Q) (H⊔J) F A x u weight d)
      (endpointIndexPotential P R H F A x u weight d)
    have hh:=hR.2 u
    rw [abs_sub_comm] at hh
    have hn:3*C*L/A.card+3*C*L/A.card=6*C*L/A.card:=by ring
    linarith only [ht,hh,hQ.2 u,hn]
end Oberwolfach
