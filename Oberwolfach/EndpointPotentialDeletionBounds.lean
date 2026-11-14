module

public import Oberwolfach.EndpointRowDeletion
public import Oberwolfach.EndpointIndexDeletion

@[expose] public section

/-! Uniform local-scale bounds on the two fixed endpoint potentials.
All original root omissions and normalizing denominators are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

theorem endpoint_potential_deletion_bounds (P R H F D E:SimpleGraph V) (A B:Finset V)
    (x:V) (weight:Sym2 V→ℝ) (d C L:ℝ) (hA:0<A.card) (hBA:B.card≤A.card)
    (hC:0≤C) (hL:0≤L)
    (hw:∀ e,e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet →
      0≤weight e/d∧weight e/d≤C/(A.card:ℝ)^2)
    (hD:∀ v,(D.degree v:ℝ)≤L) (hE:∀ v,(E.degree v:ℝ)≤L) :
    (∀ v,|endpointRowPotential P (R\D) (H\E) F A B x v weight d-
      endpointRowPotential P R H F A B x v weight d|≤5*C*L/A.card) ∧
    (∀ u,|endpointIndexPotential P (R\D) (H\E) F A x u weight d-
      endpointIndexPotential P R H F A x u weight d|≤3*C*L/A.card) := by
  have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA
  have hba:(B.card:ℝ)≤A.card:=Nat.cast_le.mpr hBA
  have hcoef:0≤C/(A.card:ℝ)^2:=by positivity
  constructor
  · intro v
    have hh:=(endpoint_row_potential_deletion P R H F D E A B x v weight d
      (C/(A.card:ℝ)^2) L hcoef (fun w hw'=>hw s(v,w) hw') (fun u _=>hE u)).2
    have hbr:B.card*((D.degree x:ℝ)+D.degree v+L)+A.card*((E.degree x:ℝ)+E.degree v)≤5*A.card*L:=by
      have h₁:=mul_le_mul_of_nonneg_left (show (D.degree x:ℝ)+D.degree v+L≤3*L by linarith [hD x,hD v]) (Nat.cast_nonneg B.card)
      have h₂:=mul_le_mul_of_nonneg_left (show (E.degree x:ℝ)+E.degree v≤2*L by linarith [hE x,hE v]) (Nat.cast_nonneg A.card)
      have h₃:=mul_le_mul_of_nonneg_right hba (show 0≤3*L by positivity)
      nlinarith only [h₁,h₂,h₃]
    apply hh.trans
    calc
      _ ≤ (C/(A.card:ℝ)^2)*(5*A.card*L):=mul_le_mul_of_nonneg_left hbr hcoef
      _ = _:=by field_simp [ne_of_gt ha]
  · intro u
    have hh:=(endpoint_index_potential_deletion P R H F D E A x u weight d
      (C/(A.card:ℝ)^2) L hcoef hw (fun v _=>hD v)).2
    apply hh.trans
    calc
      _ ≤ (C/(A.card:ℝ)^2)*A.card*(3*L):=mul_le_mul_of_nonneg_left
        (by linarith [hD x,hE u]) (by positivity)
      _ = _:=by field_simp [ne_of_gt ha]

theorem endpoint_potential_errors_after_deletion (P R H F D E:SimpleGraph V) (A B X:Finset V)
    (x:V) (weight:Sym2 V→ℝ) (targetRow targetIndex:V→ℝ) (d C L ξ:ℝ)
    (hA:0<A.card) (hBA:B.card≤A.card) (hC:0≤C) (hL:0≤L)
    (hw:∀ e,e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet →
      0≤weight e/d∧weight e/d≤C/(A.card:ℝ)^2)
    (hD:∀ v,(D.degree v:ℝ)≤L) (hE:∀ v,(E.degree v:ℝ)≤L)
    (hrow:∀ v∈X,|endpointRowPotential P R H F A B x v weight d-targetRow v|≤ξ)
    (hindex:∀ u∈B,|endpointIndexPotential P R H F A x u weight d-targetIndex u|≤ξ) :
    (∀ v∈X,|endpointRowPotential P (R\D) (H\E) F A B x v weight d-targetRow v|≤ξ+5*C*L/A.card) ∧
    (∀ u∈B,|endpointIndexPotential P (R\D) (H\E) F A x u weight d-targetIndex u|≤ξ+3*C*L/A.card) := by
  have hh:=endpoint_potential_deletion_bounds P R H F D E A B x weight d C L hA hBA hC hL hw hD hE
  constructor
  · intro v hv
    have hc:=abs_sub_le (endpointRowPotential P (R\D) (H\E) F A B x v weight d)
      (endpointRowPotential P R H F A B x v weight d) (targetRow v)
    linarith [hh.1 v,hrow v hv]
  · intro u hu
    have hc:=abs_sub_le (endpointIndexPotential P (R\D) (H\E) F A x u weight d)
      (endpointIndexPotential P R H F A x u weight d) (targetIndex u)
    linarith [hh.2 u,hindex u hu]

end Oberwolfach
