module

public import Oberwolfach.JointEventPolynomialMargins

@[expose] public section
/-! The explicit failure bound for the common retained reference event gives
the 7/10 probability needed by the enriched preparation sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem reference_event_seven_tenths
    (χ χCommon χBal χNbr qreal:ℝ) (Q:ℕ)
    (hbudget:χ+χCommon+χBal+2*χNbr<3/10) (hQ:0<Q) (hqreal:0<qreal):
    ∃ N:ℕ,1≤N ∧ ∀ n:ℕ,N≤n→∀ {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (E:Ω→Prop),
      1-χ-2/(n:ℝ)^Q-χCommon-(n:ℝ)^(-qreal)-χBal-(n:ℝ)^(-qreal)-2*χNbr-2*(n:ℝ)^(-qreal)≤μ.probability E→
      (7:ℝ)/10≤μ.probability E:=by
  have hq:(0:ℝ)<Q:=by exact_mod_cast hQ
  obtain ⟨N,hN,hbound⟩:=joint_event_polynomial_margin
    ((10/3)*(χ+χCommon+χBal+2*χNbr)) (20/3) (40/3) Q qreal (by linarith) hq hqreal
  refine ⟨N,hN,?_⟩
  intro n hn Ω _ μ E hE
  have hpowers:(n:ℝ)^(-(Q:ℝ))=((n:ℝ)^Q)⁻¹:=by
    rw [Real.rpow_neg (Nat.cast_nonneg n),Real.rpow_natCast]
  have hh:=hbound n hn
  rw [hpowers] at hh
  rw [div_eq_mul_inv] at hE
  linarith
end Oberwolfach
