module

public import Oberwolfach.EndpointPotentialDeletionBounds

@[expose] public section
/-! Endpoint root-omitted potentials are stable under both additions and
deletions, by comparing each host with their common subgraph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpoint_potential_symmetric_change_bounds
    (P R R' H H' F:SimpleGraph V) (A B:Finset V) (x:V) (weight:Sym2 V→ℝ) (d C L:ℝ)
    (hA:0<A.card) (hBA:B.card≤A.card) (hC:0≤C) (hL:0≤L)
    (hw:∀e,e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet→
      0≤weight e/d∧weight e/d≤C/(A.card:ℝ)^2)
    (hR:∀v,((R\R').degree v:ℝ)≤L) (hR':∀v,((R'\R).degree v:ℝ)≤L)
    (hH:∀v,((H\H').degree v:ℝ)≤L) (hH':∀v,((H'\H).degree v:ℝ)≤L):
    (∀v,|endpointRowPotential P R' H' F A B x v weight d-endpointRowPotential P R H F A B x v weight d|
      ≤10*C*L/A.card) ∧
    (∀u,|endpointIndexPotential P R' H' F A x u weight d-endpointIndexPotential P R H F A x u weight d|
      ≤6*C*L/A.card):=by
  let D:=R\R'
  let D':=R'\R
  let E:=H\H'
  let E':=H'\H
  letI : DecidableRel D.Adj:=Classical.decRel _
  letI : DecidableRel D'.Adj:=Classical.decRel _
  letI : DecidableRel E.Adj:=Classical.decRel _
  letI : DecidableRel E'.Adj:=Classical.decRel _
  have hd:∀v,(D.degree v:ℝ)≤L:=by convert hR using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hd':∀v,(D'.degree v:ℝ)≤L:=by convert hR' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have he:∀v,(E.degree v:ℝ)≤L:=by convert hH using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have he':∀v,(E'.degree v:ℝ)≤L:=by convert hH' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hRcommon:R\D=R'\D':=by
    ext a b
    simp only [D,D',SimpleGraph.sdiff_adj]
    tauto
  have hHcommon:H\E=H'\E':=by
    ext a b
    simp only [E,E',SimpleGraph.sdiff_adj]
    tauto
  have h1:=endpoint_potential_deletion_bounds P R H F D E A B x weight d C L hA hBA hC hL hw hd he
  have h2:=endpoint_potential_deletion_bounds P R' H' F D' E' A B x weight d C L hA hBA hC hL hw hd' he'
  constructor
  · intro v
    have he:endpointRowPotential P (R\D) (H\E) F A B x v weight d=
        endpointRowPotential P (R'\D') (H'\E') F A B x v weight d:=by rw [hRcommon,hHcommon]
    have ht:=abs_sub_le (endpointRowPotential P R' H' F A B x v weight d)
      (endpointRowPotential P (R\D) (H\E) F A B x v weight d)
      (endpointRowPotential P R H F A B x v weight d)
    have hb:=h2.1 v
    rw [←he,abs_sub_comm] at hb
    have hb1:=h1.1 v
    exact ht.trans ((add_le_add hb hb1).trans_eq (by ring))
  · intro u
    have he:endpointIndexPotential P (R\D) (H\E) F A x u weight d=
        endpointIndexPotential P (R'\D') (H'\E') F A x u weight d:=by rw [hRcommon,hHcommon]
    have ht:=abs_sub_le (endpointIndexPotential P R' H' F A x u weight d)
      (endpointIndexPotential P (R\D) (H\E) F A x u weight d)
      (endpointIndexPotential P R H F A x u weight d)
    have hb:=h2.2 u
    rw [←he,abs_sub_comm] at hb
    have hb1:=h1.2 u
    exact ht.trans ((add_le_add hb hb1).trans_eq (by ring))
end Oberwolfach
