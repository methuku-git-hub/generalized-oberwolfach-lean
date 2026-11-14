module

public import Oberwolfach.LongDiscardedHubSelectedZero
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! Convert a uniform additive error into the relative error required for
retained cycle lengths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_target_lower_bound
    (n K r:ℕ) (θ f:ℝ) (hK:0<K) (hr:0<r) (hrK:r≤K) (hθ:0≤θ)
    (hf:θ/(100*(K:ℝ))≤f):
    θ*(n:ℝ)/(100*(K:ℝ)^2)≤f*(n:ℝ)/(r:ℝ) :=by
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  have hr':0<(r:ℝ):=by exact_mod_cast hr
  have hrK':(r:ℝ)≤K:=by exact_mod_cast hrK
  have hf0:0≤f:=(by positivity : (0:ℝ)≤θ/(100*(K:ℝ))).trans hf
  have h₁:θ/(100*(K:ℝ))/(K:ℝ)≤f/(K:ℝ):=div_le_div_of_nonneg_right hf hK'.le
  have h₂:f/(K:ℝ)≤f/(r:ℝ):=div_le_div_of_nonneg_left hf0 hr' hrK'
  have h₃:=mul_le_mul_of_nonneg_right (h₁.trans h₂) (show (0:ℝ)≤n by positivity)
  have hleft:θ/(100*(K:ℝ))/(K:ℝ)*(n:ℝ)=θ*(n:ℝ)/(100*(K:ℝ)^2):=by field_simp <;> ring
  have hright:f/(r:ℝ)*(n:ℝ)=f*(n:ℝ)/(r:ℝ):=by ring
  rw [hleft,hright] at h₃
  exact h₃

theorem absolute_to_relative_frequency_error
    (a target scale c eps lam:ℝ) (hscale:0≤scale) (hc:0≤c) (hlam:0≤lam)
    (htarget:c*scale≤target) (heps:eps≤lam*c)
    (herr:|a-target|≤eps*scale):|a-target|≤lam*target:=by
  have h₁:=mul_le_mul_of_nonneg_right heps hscale
  have h₂:=mul_le_mul_of_nonneg_left htarget hlam
  calc
    |a-target|≤eps*scale:=herr
    _≤(lam*c)*scale:=h₁
    _=lam*(c*scale):=by ring
    _≤lam*target:=h₂
end Oberwolfach

namespace Oberwolfach

theorem absolute_to_relative_target_error
    (a center target scale c eps lam:ℝ) (hscale:0≤scale) (hlam:0≤lam)
    (htarget:c*scale≤target) (heps:eps≤lam*c)
    (herr:|a-center|≤eps*scale):|a-center|≤lam*target:=by
  have h₁:=mul_le_mul_of_nonneg_right heps hscale
  have h₂:=mul_le_mul_of_nonneg_left htarget hlam
  calc
    |a-center|≤eps*scale:=herr
    _≤(lam*c)*scale:=h₁
    _=lam*(c*scale):=by ring
    _≤lam*target:=h₂
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U]

theorem long_kept_fraction_zero_or_retained
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ:ℝ) (i:Fin K) (u:U):
    longAssignedKeptFraction F hF K θ i u=0 ∨
      θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u :=by
  unfold longAssignedKeptFraction
  split_ifs with h
  · exact Or.inr h
  · exact Or.inl rfl
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U]

theorem long_retained_hub_padded_length_exact
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0<θ) (i:Fin K) (u:U)
    (hf:θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u):
    longPaddedSeedExponent i+2=i.val+1 :=by
  have hK:0<K:=Nat.zero_lt_of_lt i.isLt
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  have hfrac:0<longAssignedKeptFraction F hF K θ i u:=
    (show 0<θ/(100*(K:ℝ)) by positivity).trans_le hf
  have hr : (3:ℕ) ≤ (i:Fin K).val + 1 := by
    by_contra h
    have hz:longAssignedKeptFraction F hF K θ i u=0:=
      (long_assigned_kept_below_three_zero F hF K i (by omega) θ u).1
    rw [hz] at hfrac
    exact (lt_irrefl (0:ℝ)) hfrac
  rw [long_padded_seed_length_eq_exponent]
  exact long_assigned_padded_length_true i hr
end Oberwolfach
