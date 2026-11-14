module

public import Oberwolfach.FiniteSeedFailureMargins

@[expose] public section
/-! A fixed linear hub-count tolerance makes the spoke-count failure
uniformly small before the vertex order and hub set are chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem eventually_assigned_spoke_failure_below
    (d:ℕ) (ξ δ:ℝ) (hξ:0<ξ) (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀U:Type,[Fintype U]→Fintype.card U≤n→
      4*(Fintype.card U:ℝ)*Real.exp
        (-2*(ξ*(n:ℝ))^2/((4*(d:ℝ)+3)^2*(n:ℝ)))<δ :=by
  let c:ℝ:=2*ξ^2/(4*(d:ℝ)+3)^2
  have hc:0<c:=by dsimp [c]; positivity
  obtain ⟨N,hN⟩:=eventually_any_polynomial_exponential_failure_below 4 c δ 1 hc hδ
  refine ⟨max N 1,?_⟩
  intro n hn U _ hu
  have hnN:N≤n:=(le_max_left _ _).trans hn
  have hnpos:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hexp:-2*(ξ*(n:ℝ))^2/((4*(d:ℝ)+3)^2*(n:ℝ))= -c*(n:ℝ):=by
    dsimp [c]
    field_simp
    <;> ring
  rw [hexp]
  have hcard:(Fintype.card U:ℝ)≤n:=by exact_mod_cast hu
  have hmul:=mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg (-c*(n:ℝ)))
  have hh:=hN n hnN
  simp only [pow_one] at hh
  nlinarith
end Oberwolfach
