module

public import Oberwolfach.FloorOrbit

@[expose] public section

/-! The real degree centres from the independently rounded index sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem rounded_vortex_centre_error {ε ρ ρ₀ D : ℝ}
    (he : 0 ≤ ε) (heq : ε < 1 / 4) (hp : 0 < ρ₀) (hρ : ρ₀ ≤ ρ)
    {n u : ℕ} (hn : 0 < n)
    (hu : (u : ℝ) ≤ (n : ℝ) / 2) (hcentre : 2 * (u : ℝ) = ρ * D) (i : ℕ) :
    |2 * (floorOrbit ε u i : ℝ) / ρ -
      (D / n) * floorOrbit ε n i| < 3 / ρ₀ := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hρpos : 0 < ρ := hp.trans_le hρ
  let a := (u : ℝ) / n
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ hnreal).mpr
    linarith
  have hinit : (u : ℝ) = a * n := by dsimp [a]; field_simp
  have hr := floorOrbit_rounding_error he (by linarith) ha ha1 hinit i
  have hden : 0 < 1 - ε := by linarith
  have hone : 1 / (1 - ε) < (3 / 2 : ℝ) := by
    apply (div_lt_iff₀ hden).mpr
    linarith
  have herr : |(floorOrbit ε u i : ℝ) - a * floorOrbit ε n i| < 3 / 2 := hr.trans hone
  have hcoef : (2 / ρ) * a = D / n := by
    dsimp [a]
    field_simp
    nlinarith [hcentre]
  have heq' : 2 * (floorOrbit ε u i : ℝ) / ρ - (D / n) * floorOrbit ε n i =
      (2 / ρ) * ((floorOrbit ε u i : ℝ) - a * floorOrbit ε n i) := by
    rw [← hcoef]
    ring
  rw [heq', abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / ρ)]
  calc
    _ < (2 / ρ) * (3 / 2) := mul_lt_mul_of_pos_left herr (by positivity)
    _ = 3 / ρ := by ring
    _ ≤ 3 / ρ₀ := div_le_div_of_nonneg_left (by norm_num) hp hρ

end Oberwolfach
