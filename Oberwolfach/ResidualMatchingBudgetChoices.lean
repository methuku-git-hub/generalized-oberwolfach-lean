module

public import Oberwolfach.ResidualMatchingCapacityFromBounds

@[expose] public section
/-! A convenient numerical consequence of the original small-parameter
hierarchy for the matching capacity calculation. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem residual_matching_budget_of_small_parameters
    (d:ℕ) (hd:0<d) (θ α b lam η z:ℝ) (hθ:0<θ) (hθ1:θ≤1)
    (hα:0<α) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hinv:1/(d:ℝ)≤θ/1024) (hη:η≤lam/(10*(d:ℝ)))
    (hb:b≤α*θ/1024) (hz:z≤θ/1024):
    16/(d:ℝ)+16*η+16*b/α+4*z≤θ/8:=by
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hinv0:0≤1/(d:ℝ):=by positivity
  have hdiv:lam/(10*(d:ℝ))≤θ/1024:=by
    have hlam1:lam≤1:=by linarith
    have hscale:lam*(1/(d:ℝ))≤1/(d:ℝ):=by nlinarith
    have heq:lam/(10*(d:ℝ))=lam*(1/(d:ℝ))/10:=by ring
    nlinarith
  have hb':b/α≤θ/1024:=by
    apply (div_le_iff₀ hα).2
    nlinarith
  have hη':η≤θ/1024:=hη.trans hdiv
  ring_nf at hinv hη' hb' hz ⊢
  linarith
end Oberwolfach
