module

public import Oberwolfach.HubTestMassMargin

@[expose] public section
/-! Fixed absolute root and count tolerances imply a relative retained
frequency error once the original retained-frequency floor is used. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem retained_mass_relative_budget
    (n card b pstar η f fmin θ lam t τ countErr:ℝ)
    (hn:0≤n) (hcard:0≤card) (hcardmax:card≤n)
    (hpstar:0<pstar) (hb:pstar≤b) (hη:0≤η)
    (hfmin:0≤fmin) (hf:fmin≤f) (hθ0:0≤θ) (hθ1:θ≤1)
    (hlam:0≤lam) (ht0:0≤t) (hτ0:0≤τ) (hcount0:0≤countErr)
    (hbalance:η*b=(1-θ)*f)
    (ht:t≤lam*fmin/4) (hτ:τ≤lam*pstar/4) (hcount:countErr≤lam*pstar*n/4):
    card*(t+τ*η)+η*countErr≤lam*f*n :=by
  have hf0:0≤f:=hfmin.trans hf
  have hηp:η*pstar≤f:=by
    have hh:=mul_le_mul_of_nonneg_left hb hη
    have hfθ:0≤θ*f:=mul_nonneg hθ0 hf0
    nlinarith
  have hte:t≤lam*f/4:=by
    have hh:=mul_le_mul_of_nonneg_left hf hlam
    nlinarith
  have hτe:τ*η≤lam*f/4:=by
    have hh:=mul_le_mul_of_nonneg_right hτ hη
    have hh':=mul_le_mul_of_nonneg_left hηp hlam
    nlinarith
  have hce:η*countErr≤lam*f*n/4:=by
    have hh:=mul_le_mul_of_nonneg_left hcount hη
    have hh':=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hηp hlam) hn
    nlinarith
  have hnon:0≤t+τ*η:=by positivity
  have hrow:=mul_le_mul_of_nonneg_right hcardmax hnon
  have hbnd:=mul_le_mul_of_nonneg_left (add_le_add hte hτe) hn
  nlinarith [mul_nonneg (mul_nonneg hlam hf0) hn]
end Oberwolfach
