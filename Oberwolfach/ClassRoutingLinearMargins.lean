module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
/-! A linear discrepancy and a linear forbidden budget admit routing at a
scale chosen before the order; only the order threshold is enlarged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem class_routing_linear_margins
    (c q ζ β:ℝ) (hc:0≤c) (hq:0<q)
    (hgap:c/q+2*c+4*q+2*ζ<β):
    ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→∀a f:ℝ,
      0≤a→a≤c*n→f≤ζ*n→
      let L:=Nat.ceil (q*n)
      0<L ∧ (n:ℝ)*a/L+2*a+4*L+2*f<β*n ∧
        a+2*L≤(c+2*q)*n+2:=by
  let gap:=β-(c/q+2*c+4*q+2*ζ)
  have hgapPos:0<gap:=by dsimp [gap];linarith
  obtain ⟨N,hN⟩:=exists_nat_gt (4/gap)
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn a f ha hac hf L
  have hnpos:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hnN:(N:ℝ)≤n:=by exact_mod_cast (show N≤n by omega)
  have hsmall:4<gap*n:=by
    have hh:(4/gap:ℝ)<n:=lt_of_lt_of_le hN hnN
    simpa [mul_comm] using (div_lt_iff₀ hgapPos).mp hh
  have hLlo:q*(n:ℝ)≤(L:ℝ):=Nat.le_ceil _
  have hLhi:(L:ℝ)<q*n+1:=Nat.ceil_lt_add_one (by positivity)
  have hLpos:0<L:=by
    have hp:0<(L:ℝ):=lt_of_lt_of_le (mul_pos hq hnpos) hLlo
    exact_mod_cast hp
  have hLposR:0<(L:ℝ):=by exact_mod_cast hLpos
  have hdiv:(n:ℝ)*a/L≤(c/q)*n:=by
    apply (div_le_iff₀ hLposR).2
    have hcq:0≤c/q:=div_nonneg hc hq.le
    have hh:=mul_le_mul_of_nonneg_left hLlo hcq
    have heq:(c/q)*(q*(n:ℝ))=c*n:=by field_simp
    rw [heq] at hh
    have hnac:=mul_le_mul_of_nonneg_left hac hnpos.le
    have hh' := mul_le_mul_of_nonneg_left hh hnpos.le
    nlinarith [hh']
  refine ⟨hLpos,?_,?_⟩
  · dsimp [gap] at hsmall
    nlinarith
  · nlinarith
end Oberwolfach
