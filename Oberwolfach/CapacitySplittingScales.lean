module

public import Mathlib.Tactic

@[expose] public section

/-! Numerical substitutions for the signed corrections in the marked-capacity
position splitting. No separation parameter enters these choices. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_position_signed_scale (ε ρ δ d A n mean : ℝ)
    (hρ : 0<ρ) (hδ : 0<δ) (hd : 0<d) (hA : 24/(δ*d)≤A) (hn : 0<n)
    (hε : ε≤δ*d/16) (hmean : d*n/2≤mean) :
    (A*ρ)*(2*ε*n)+3*(ρ*n) ≤ δ*(A*ρ)*mean := by
  have hAp : 0<A := (div_pos (by norm_num) (mul_pos hδ hd)).trans_le hA
  have hAmul : 24≤A*(δ*d) := (div_le_iff₀ (mul_pos hδ hd)).mp hA
  have heps := mul_le_mul_of_nonneg_left hε hAp.le
  have hbase : A*(2*ε)+3≤δ*A*d/2 := by nlinarith
  calc
    _ = (A*(2*ε)+3)*(ρ*n) := by ring
    _ ≤ (δ*A*d/2)*(ρ*n) := mul_le_mul_of_nonneg_right hbase (mul_pos hρ hn).le
    _ = (δ*(A*ρ))*(d*n/2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean (mul_pos hδ (mul_pos hAp hρ)).le

theorem normalized_correction_mass_bound (edges n B h : ℝ)
    (he : edges≤n^2) (hB : 0<B) (hh : 0<h) (hscale : 2/h≤B) :
    edges/B ≤ h*n*n/2 := by
  have hBh : 2≤B*h := (div_le_iff₀ hh).mp hscale
  have hm := mul_le_mul_of_nonneg_right hBh (sq_nonneg n)
  apply (div_le_iff₀ hB).mpr
  nlinarith

theorem exists_capacity_splitting_parameters (k : ℕ) (δ d q A B : ℝ)
    (hδ : 0<δ) (hd : 0<d) (hq : 0<q) (hA : 0<A) (hB : 0<B) :
    ∃ ε κ : ℝ,0<ε ∧ 0<κ ∧ ε≤δ*d/16 ∧ κ≤1/2 ∧
      2*(ε+κ)≤q/10 ∧ κ/(k+1:ℝ)+k*(B*A*(ε+κ))≤1/(2*(k+1:ℝ)) := by
  let C : ℝ := 1/(k+1:ℝ)+2*k*B*A
  have hC : 0<C := by unfold C;positivity
  let η := min (δ*d/16) (min (1/2) (min (q/40) (1/(2*(k+1:ℝ)*C))))/2
  have hη : 0<η := by unfold η;positivity
  have hle : η≤min (δ*d/16) (min (1/2) (min (q/40) (1/(2*(k+1:ℝ)*C)))) := by
    dsimp only [η]
    have hp : 0<min (δ*d/16) (min (1/2) (min (q/40) (1/(2*(k+1:ℝ)*C)))) := by positivity
    linarith
  have he := hle.trans (min_le_left _ _)
  have hk := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hq' := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc := hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨η,η,hη,hη,he,hk,by linarith,?_⟩
  have hm := mul_le_mul_of_nonneg_right hc hC.le
  have hid : (1/(2*(k+1:ℝ)*C))*C=1/(2*(k+1:ℝ)) := by field_simp
  rw [hid] at hm
  convert hm using 1 <;> dsimp [C] <;> ring

end Oberwolfach
