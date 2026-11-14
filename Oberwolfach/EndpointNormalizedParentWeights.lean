module

public import Oberwolfach.EndpointWeightNormalization

@[expose] public section
/-! The parent matching's edgewise bounds give the normalized bounds needed
for stability of the endpoint potentials. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem endpoint_normalized_parent_weight_bounds
    (P F:SimpleGraph V) (A B:Finset V) (x:V) (weight:Sym2 V→ℝ)
    (κ p q s c C:ℝ) (ha:0<(A.card:ℝ)) (hκ:0<κ) (hp:0<p) (hc:0≤c) (hC:0≤C)
    (hb:κ*A.card≤(B.card:ℝ)) (hba:B.card≤A.card)
    (hq:p≤q) (hq1:q≤1) (hs:p≤s) (hs1:s≤1)
    (hpositive:∀e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
      c/A.card≤weight e ∧ weight e≤C/A.card):
    ∀e,e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet→
      0≤weight e/(B.card*q^2*s^3) ∧
      weight e/(B.card*q^2*s^3)≤(C/(κ*p^5))/(A.card:ℝ)^2:=by
  intro e he
  have hw:=hpositive e he
  have hw0:0≤weight e:=(div_nonneg hc ha.le).trans hw.1
  have hbpos:0<(B.card:ℝ):=(mul_pos hκ ha).trans_le hb
  have hqpos:0<q:=hp.trans_le hq
  have hspos:0<s:=hp.trans_le hs
  have hd:0≤(B.card:ℝ)*q^2*s^3:=by positivity
  exact ⟨div_nonneg hw0 hd,
    (endpoint_triangle_coefficient_bounds A.card B.card κ p q s c C (weight e)
      ha hκ hp hc hC hb (by exact_mod_cast hba) hq hq1 hs hs1 hw).2⟩
end Oberwolfach
