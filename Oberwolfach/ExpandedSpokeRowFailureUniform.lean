module

public import Oberwolfach.LongAssignedSpokeFailureUniform

@[expose] public section
/-! Linear row-count tolerance makes the variable-density spoke-row
failure uniformly small when the number of hubs is at most the host order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem eventually_spoke_row_failure_below
    (d:ℕ) (ξ δ:ℝ) (hξ:0<ξ) (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀U:Type,[Fintype U]→0<Fintype.card U→Fintype.card U≤n→
      4*(n:ℝ)*Real.exp (-2*(ξ*(n:ℝ))^2/((4*(d:ℝ)+3)^2*(Fintype.card U:ℝ)))<δ :=by
  obtain ⟨N,hN⟩:=eventually_assigned_spoke_failure_below d ξ δ hξ hδ
  refine ⟨max N 1,?_⟩
  intro n hn U _ hU hUn
  have hn0:0<n:=by omega
  have hnR:0<(n:ℝ):=by exact_mod_cast hn0
  have hUR:0<(Fintype.card U:ℝ):=by exact_mod_cast hU
  have hu:(Fintype.card U:ℝ)≤n:=by exact_mod_cast hUn
  have hden:0<(4*(d:ℝ)+3)^2*(Fintype.card U:ℝ):=by positivity
  have hdenn:0<(4*(d:ℝ)+3)^2*(n:ℝ):=by positivity
  have hdencmp:(4*(d:ℝ)+3)^2*(Fintype.card U:ℝ)≤(4*(d:ℝ)+3)^2*(n:ℝ):=
    mul_le_mul_of_nonneg_left hu (sq_nonneg _)
  have hnum: -2*(ξ*(n:ℝ))^2≤0:=by nlinarith [sq_nonneg (ξ*(n:ℝ))]
  have hexp:-2*(ξ*(n:ℝ))^2/((4*(d:ℝ)+3)^2*(Fintype.card U:ℝ))≤
      -2*(ξ*(n:ℝ))^2/((4*(d:ℝ)+3)^2*(n:ℝ)):=by
    apply (div_le_div_iff₀ hden hdenn).2
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hnum (sub_nonneg.mpr hdencmp)]
  have hh:=hN n (by omega) (Fin n) (by simp)
  simp only [Fintype.card_fin] at hh
  have hb:=mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity : 0≤4*(n:ℝ))
  exact lt_of_le_of_lt hb hh
end Oberwolfach
