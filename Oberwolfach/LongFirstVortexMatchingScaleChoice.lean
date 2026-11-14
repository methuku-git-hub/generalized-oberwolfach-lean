module

public import Oberwolfach.LongOrderedMatchingResidualRates

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_first_vortex_matching_scale_choice
    (d:ℕ) (θ lam ε δold a γ:ℝ) (n:ℕ) (inner:ℝ)
    (hd:0<d) (hθ:0<θ) (hlam:0<lam) (hε:0<ε)
    (hδ:0≤δold) (hδ1:δold≤1) (hlamδ:lam≤δold*ε/32)
    (hinv:1/(d:ℝ)≤θ/1024) (ha:a≤lam/(10*(d:ℝ))) (hγ:γ≤lam/(10*(d:ℝ)))
    (hinner:(ε/2)*(n:ℝ)≤ inner):
    0<θ/4096 ∧ θ/4096≤θ/4096 ∧ max a γ*(n:ℝ)≤(θ/4096)*inner := by
  have hdpos:0<(d:ℝ):=by exact_mod_cast hd
  have hlamBound:lam≤ε/32:=by nlinarith [mul_nonneg (sub_nonneg.mpr hδ1) hε.le]
  have hrate:lam/(10*(d:ℝ))≤ε*θ/8192:=by
    have h1:=mul_le_mul_of_nonneg_left hinv (show 0≤lam/10 by positivity)
    have h2:=mul_le_mul_of_nonneg_right hlamBound hθ.le
    have hid:lam/(10*(d:ℝ))=(lam/10)*(1/(d:ℝ)):=by field_simp
    rw [hid]
    nlinarith
  refine ⟨by positivity,le_rfl,?_⟩
  have hmax:max a γ≤ε*θ/8192:=max_le (ha.trans hrate) (hγ.trans hrate)
  have hn:(0:ℝ)≤n:=by positivity
  have hleft:=mul_le_mul_of_nonneg_right hmax hn
  have hright:=mul_le_mul_of_nonneg_left hinner (show 0≤θ/4096 by positivity)
  nlinarith
end Oberwolfach
