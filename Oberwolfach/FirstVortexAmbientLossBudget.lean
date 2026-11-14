module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
/-! Discharge the ambient loss and protected-degree budgets using a global
scale fixed before the later local balance cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_ambient_loss_budget
    (δ loss:ℝ) (d:ℕ) (hδ:0<δ) (hδsmall:δ≤1/4)
    (hloss:5*Real.sqrt δ≤loss):
    ∃N:ℕ,∀n:ℕ,N≤n→∀κ εInner:ℝ,
      0≤κ→κ≤Real.sqrt δ/4→0≤εInner→εInner≤δ/8→
      δ+κ≤Real.sqrt δ ∧
      2*(δ*(n:ℝ)+(κ*(n:ℝ)+1))≤loss*(n:ℝ) ∧
      εInner*(n:ℝ)+((6*d+2:ℕ):ℝ)≤δ*(n:ℝ)/4 :=by
  have hs:0<Real.sqrt δ:=Real.sqrt_pos.2 hδ
  have hs2:Real.sqrt δ≤1/2:=Real.sqrt_le_iff.mpr ⟨by norm_num,by nlinarith⟩
  have hsq:Real.sqrt δ*Real.sqrt δ=δ:=Real.mul_self_sqrt hδ.le
  have hδsqrt:δ≤Real.sqrt δ/2:=by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs2)]
  obtain ⟨N1,hN1⟩:=exists_nat_gt (4/Real.sqrt δ)
  obtain ⟨N2,hN2⟩:=exists_nat_gt (8*((6*d+2:ℕ):ℝ)/δ)
  refine ⟨max N1 N2,?_⟩
  intro n hn κ εInner hκ hκsmall he heSmall
  have hn1:N1≤n:=le_trans (le_max_left _ _) hn
  have hn2:N2≤n:=le_trans (le_max_right _ _) hn
  have hn1R:(N1:ℝ)≤n:=by exact_mod_cast hn1
  have hn2R:(N2:ℝ)≤n:=by exact_mod_cast hn2
  have hnR:0≤(n:ℝ):=Nat.cast_nonneg n
  have hone:4≤Real.sqrt δ*(n:ℝ):=by
    have hh:(4/Real.sqrt δ)<(n:ℝ):=lt_of_lt_of_le hN1 hn1R
    simpa only [mul_comm] using le_of_lt ((div_lt_iff₀ hs).mp hh)
  have hfixed:8*((6*d+2:ℕ):ℝ)≤δ*(n:ℝ):=by
    have hh:8*((6*d+2:ℕ):ℝ)/δ<(n:ℝ):=lt_of_lt_of_le hN2 hn2R
    simpa only [mul_comm] using le_of_lt ((div_lt_iff₀ hδ).mp hh)
  have hκn:=mul_le_mul_of_nonneg_right hκsmall hnR
  have hδn:=mul_le_mul_of_nonneg_right hδsqrt hnR
  have hLossn:=mul_le_mul_of_nonneg_right hloss hnR
  have hen:=mul_le_mul_of_nonneg_right heSmall hnR
  constructor
  · linarith
  constructor <;> nlinarith
end Oberwolfach
