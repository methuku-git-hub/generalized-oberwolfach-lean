module

public import Oberwolfach.ColourRoundLargeDegree

@[expose] public section

/-! Degree bounds at every stage are compared to the current list size,
using one lower scale chosen before the finite iteration. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Oberwolfach

theorem colour_iteration_scale_bounds
    (k D l s nC B : ℕ) (hD : 0<D) (hs : s≤l) (hl : l≤2*D) (hC : nC≤2*D)
    {a δ : ℝ} (ha : 0<a) (hδ : 0<δ) (hδ1 : δ≤1)
    (hlow : a*D≤l) (hB : (B : ℝ)≤(D : ℝ)^(1-δ)) :
    let K := 1+(a^(1-δ))⁻¹+5*(k : ℝ)/(a^2)
    1≤K ∧ (B : ℝ)≤K*(l : ℝ)^(1-δ) ∧
      ((k*(D+nC*s) : ℕ) : ℝ)≤K*(l : ℝ)^2 := by
  let K := 1+(a^(1-δ))⁻¹+5*(k : ℝ)/(a^2)
  have ha2 : 0<a^2 := sq_pos_of_pos ha
  have hap : 0<a^(1-δ) := Real.rpow_pos_of_pos ha _
  have hinv : 0≤(a^(1-δ))⁻¹ := inv_nonneg.mpr hap.le
  have hdiv : 0≤5*(k : ℝ)/(a^2) := by positivity
  have hK1 : 1≤K := by dsimp [K];linarith
  have hKpow : (a^(1-δ))⁻¹≤K := by dsimp [K];linarith
  have hKsq : 5*(k : ℝ)/(a^2)≤K := by dsimp [K];linarith
  have hDR : (1 : ℝ)≤D := by exact_mod_cast hD
  have hlR : (l : ℝ)≤2*(D : ℝ) := by exact_mod_cast hl
  have hsR : (s : ℝ)≤l := by exact_mod_cast hs
  have hCR : (nC : ℝ)≤2*(D : ℝ) := by exact_mod_cast hC
  have hlow0 : 0≤a*(D : ℝ) := by positivity
  have hpow : a^(1-δ)*(D : ℝ)^(1-δ)≤(l : ℝ)^(1-δ) := by
    rw [← Real.mul_rpow ha.le (Nat.cast_nonneg D)]
    exact Real.rpow_le_rpow hlow0 hlow (by linarith)
  have hscale : (D : ℝ)^(1-δ)≤(a^(1-δ))⁻¹*(l : ℝ)^(1-δ) := by
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hap).mpr
    simpa only [mul_comm] using hpow
  have hB' : (B : ℝ)≤K*(l : ℝ)^(1-δ) := hB.trans
    (hscale.trans (mul_le_mul_of_nonneg_right hKpow (by positivity)))
  have hdeg : ((k*(D+nC*s) : ℕ) : ℝ)≤5*(k : ℝ)*(D : ℝ)^2 := by
    push_cast
    have hsc : (nC : ℝ)*(s : ℝ)≤4*(D : ℝ)^2 := by
      have hh := mul_le_mul hCR (hsR.trans hlR) (Nat.cast_nonneg s) (by positivity : 0≤2*(D : ℝ))
      nlinarith
    have hh : (D : ℝ)+nC*s≤5*(D : ℝ)^2 := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg k)
    nlinarith
  have hsq : a^2*(D : ℝ)^2≤(l : ℝ)^2 := by nlinarith [sq_nonneg ((l : ℝ)-a*D)]
  have hscale2 : 5*(k : ℝ)*(D : ℝ)^2≤(5*(k : ℝ)/(a^2))*(l : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hsq (show 0≤5*(k : ℝ)/(a^2) by positivity)
    have he : (5*(k : ℝ)/(a^2))*(a^2*(D : ℝ)^2)=5*(k : ℝ)*(D : ℝ)^2 := by field_simp
    rw [he] at hh
    exact hh
  exact ⟨hK1,hB',hdeg.trans (hscale2.trans
    (mul_le_mul_of_nonneg_right hKsq (sq_nonneg (l : ℝ))))⟩

end Oberwolfach
