module

public import Oberwolfach.VortexRemovedStarScales

@[expose] public section
/-! Explicit size and comparison constants for the active differences.
These are deterministic prerequisites for applying a fixed-domain event;
they do not assert that such an event has been constructed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem vortex_sdiff_size_bounds
    (V:ℕ→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    (I T:∀ i,Finset (V i)) (L:ℕ) (θ η K m:ℝ) (X:ℕ→ℝ)
    (hθ0:0≤θ) (hθ1:θ<1) (hη:0≤η) (hK:0≤K)
    (hsub:∀ i,i≤L→T i⊆I i)
    (hsmall:∀ i,i≤L→((T i).card:ℝ)≤θ*(I i).card)
    (hstep:∀ i,i<L→((I (i+1)).card:ℝ)≤η*(I i).card)
    (hmin:∀ i,i≤L→m≤(1-θ)*((I i).card:ℝ))
    (hX:∀ i,i≤L→X i≤K*((I i).card:ℝ)):
    (∀ i,i≤L→m≤((I i\T i).card:ℝ)) ∧
    (∀ i,i≤L→X i≤(K/(1-θ))*((I i\T i).card:ℝ)):=by
  have hden:0<1-θ:=by linarith
  have hlo:=(vortex_sdiff_scales V I T L θ η hθ0 hθ1 hη hsub hsmall hstep).1
  constructor
  · intro i hi
    exact (hmin i hi).trans (hlo i hi)
  · intro i hi
    have hcur:=hlo i hi
    have hmul:0≤K*(((I i\T i).card:ℝ)-(1-θ)*((I i).card:ℝ)):=mul_nonneg hK (sub_nonneg.mpr hcur)
    have hbound:K*((I i).card:ℝ)≤(K/(1-θ))*((I i\T i).card:ℝ):=by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hden).2
      nlinarith
    exact (hX i hi).trans hbound
end Oberwolfach
