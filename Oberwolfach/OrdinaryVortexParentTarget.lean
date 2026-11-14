module

public import Oberwolfach.OrdinaryParentCrossTarget
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! The original vortex degree profile and rim/spoke marginal identity
supply the fixed inner-pair balance target. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_vortex_parent_cross_target
    (P:SimpleGraph V) (I:Finset V) (J:Finset U) (ρ pH pR δ:ℝ)
    (hρ:0<ρ) (hpR:0≤pR) (hpR1:pR≤1) (hδ:0≤δ) (hprob:pR=ρ*pH)
    (hprofile:∀v,|((P.neighborFinset v∩I).card:ℝ)-2*J.card/ρ|≤δ):
    ∀v,|pR*(P.neighborFinset v∩I).card-2*pH*J.card|≤δ:=by
  have hidentity:pR*(2*(J.card:ℝ)/ρ)=2*pH*J.card:=by
    rw [hprob]
    field_simp
    <;> ring
  intro v
  exact ordinary_parent_cross_target _ _ pR pH J.card δ hpR hpR1 hδ (hprofile v) hidentity
end Oberwolfach
