module

public import Oberwolfach.AsymptoticMargins
public import Oberwolfach.RandomColourCuts

@[expose] public section

/-! Numerical margins for common configuration events. Constants and the order
threshold are chosen before the host, sample marginals, or root-index sets. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem linear_deviation_failure_exponential (C A ε : ℝ)
    (hA : 0<A) (hε : 0<ε) (K : ℕ) :
    ∀ n : ℕ,0<n → ∀ M D : ℝ,0≤M → M≤C*(n:ℝ)^K →
      0<D → D≤A*n →
      M*(2*Real.exp (-2*(ε*n)^2/D))≤2*C*(n:ℝ)^K*Real.exp (-(2*ε^2/A)*n) := by
  intro n hn M D hM hMb hD hDb
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hex : -2*(ε*n)^2/D≤-(2*ε^2/A)*n := by
    apply (div_le_iff₀ hD).mpr
    have hmul := mul_le_mul_of_nonneg_left hDb (by positivity : 0≤2*ε^2/A*n)
    have heq : (2*ε^2/A*n)*(A*n)=2*(ε*n)^2 := by field_simp <;> ring
    rw [heq] at hmul
    nlinarith only [hmul]
  calc
    _ ≤ M*(2*Real.exp (-(2*ε^2/A)*n)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (by norm_num)) hM
    _ ≤ (C*(n:ℝ)^K)*(2*Real.exp (-(2*ε^2/A)*n)) :=
      mul_le_mul_of_nonneg_right hMb (by positivity)
    _ = (2*C)*(n:ℝ)^K*Real.exp (-(2*ε^2/A)*n) := by ring

theorem constant_deviation_failure_exponential (C A t : ℝ)
    (hA : 0<A) (ht : 0<t) (K : ℕ) :
    ∀ n : ℕ,0<n → ∀ M : ℝ,0≤M → M≤C*(n:ℝ)^K →
      M*(2*Real.exp (-2*t^2/(A/n)))≤2*C*(n:ℝ)^K*Real.exp (-(2*t^2/A)*n) := by
  intro n hn M hM hMb
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hex : -2*t^2/(A/n)=-(2*t^2/A)*n := by field_simp <;> ring
  rw [hex]
  calc
    _ ≤ (C*(n:ℝ)^K)*(2*Real.exp (-(2*t^2/A)*n)) :=
      mul_le_mul_of_nonneg_right hMb (by positivity)
    _ = (2*C)*(n:ℝ)^K*Real.exp (-(2*t^2/A)*n) := by ring


end Oberwolfach
