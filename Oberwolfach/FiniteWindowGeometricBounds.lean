module

public import Mathlib.Tactic

@[expose] public section
/-! Iterated bounded ratios control every term in a finite recent window. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finite_window_step_power_bound
    (a:ℕ→ℝ) (K:ℝ) (i:ℕ) (hK:0≤K)
    (hstep:∀j < i,a j≤K*a (j+1)):
    ∀j ≤ i,a j≤K^(i-j)*a i :=by
  intro j hji
  have hgen:∀t:ℕ,j ≤ t→t ≤ i→a j≤K^(t-j)*a t:=by
    intro t hjt
    induction hjt with
    | refl => intro _;simp
    | @step n hn ih =>
      intro hni
      have hrec:=ih (by omega)
      have hstepn:=hstep n (by omega)
      have hmul:=mul_le_mul_of_nonneg_left hstepn (pow_nonneg hK (n-j))
      have hnj:j ≤ n:=hn
      have heq:n+1-j=(n-j)+1:=by omega
      rw [heq,pow_succ]
      nlinarith only [hrec,hmul]
  exact hgen i hji le_rfl

theorem finite_window_sum_uniform_bound
    (J:Finset ℕ) (a:ℕ→ℝ) (c B:ℝ)
    (hc:0≤c) (hB:0≤B) (hcard:(J.card:ℝ)≤B) (hbound:∀j∈J,a j≤c):
    ∑j∈J,a j≤B*c :=by
  calc
    ∑j∈J,a j≤∑_j∈J,c:=Finset.sum_le_sum hbound
    _=(J.card:ℝ)*c:=by simp
    _≤B*c:=mul_le_mul_of_nonneg_right hcard hc
end Oberwolfach
