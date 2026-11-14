module

public import Oberwolfach.AbsorberRestrictionScales

@[expose] public section

/-! Rescale the unchanged ambient coefficients to |T'|/r. These constants
depend on the original density lower bound and not on later forbidden sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem ordinary_profile_weight_rescale (r : ℕ) (hr : 1≤r)
    (n k β b B w : ℝ) (hn : 0<n) (hk : 0<k) (hβ : 0<β)
    (hb : 0≤b) (hB : 0≤B) (hlow : β*n/2≤r*k) (hhigh : (r:ℝ)*k≤n)
    (hw : b/n^(r-1)≤w ∧ w≤B/n^(r-1)) :
    (b*(β/2)^(r-1)/(r:ℝ)^(r-1))/k^(r-1)≤w ∧
      w≤(B/(r:ℝ)^(r-1))/k^(r-1) := by
  have hrR : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hden : (β/2*n)^(r-1)≤((r:ℝ)*k)^(r-1) :=
    pow_le_pow_left₀ (by positivity) (by nlinarith only [hlow]) _
  have hden' : (β/2)^(r-1)*n^(r-1)≤(r:ℝ)^(r-1)*k^(r-1) := by
    simpa only [mul_pow] using hden
  constructor
  · apply le_trans _ hw.1
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<(r:ℝ)^(r-1)*k^(r-1)) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hden' hb]
  · apply hw.2.trans
    rw [div_div]
    apply div_le_div_of_nonneg_left hB (by positivity)
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hhigh (r-1)

theorem ordinary_profile_absorber_rescale (r : ℕ) (a n k count : ℝ)
    (ha : 0≤a) (hk : 0≤k) (hhigh : (r:ℝ)*k≤n)
    (hcount : (a/2)*n^(r*r)≤count) :
    ((a/2)*(r:ℝ)^(r*r))*k^(r*r)≤count := by
  apply le_trans _ hcount
  calc
    _ = (a/2)*((r:ℝ)*k)^(r*r) := by rw [mul_pow];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hhigh _) (by positivity)

end Oberwolfach
