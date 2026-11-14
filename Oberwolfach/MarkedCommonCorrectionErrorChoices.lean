module

public import Mathlib.Tactic

@[expose] public section
/-! Choose reference and neighbourhood errors after the sparse correction
tolerance, including the cut-change and global-balance budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_common_correction_error_choices (m:ℕ) (h η₀:ℝ) (hh:0<h) (hη:0<η₀):
    ∃εRef εNbr:ℝ,0<εRef ∧ 0<εNbr ∧
      2*εRef+2*εNbr≤η₀ ∧ εRef+εNbr≤η₀ ∧ ((m:ℝ)+1)*εNbr≤η₀ ∧
      (∀hNbr:ℕ,εNbr/(2*((hNbr:ℝ)+1))≤14*h) ∧
      ∀(n u:ℕ),u≤n→
        2*(εRef*n)+2*(εNbr*u)≤η₀*n ∧
        εRef*n+εNbr*u≤η₀*n ∧
        (((m:ℝ)+1)*(εNbr*n))≤η₀*n:=by
  let c:ℝ:=(m:ℝ)+1
  have hc:1≤c:=by
    have hm:0≤(m:ℝ):=Nat.cast_nonneg _
    dsimp [c];linarith
  let εRef:=η₀/16
  let εNbr:=min (η₀/(16*c)) h
  have hR:0<εRef:=by dsimp [εRef];positivity
  have hN:0<εNbr:=by dsimp [εNbr];positivity
  have hNh:εNbr≤h:=min_le_right _ _
  have hNcap:εNbr≤η₀/(16*c):=min_le_left _ _
  have hcoeff:εNbr*(16*c)≤η₀:=(le_div_iff₀ (by positivity)).mp hNcap
  have hNsmall:εNbr≤η₀/16:=by nlinarith [mul_nonneg (sub_nonneg.mpr hc) hN.le]
  have hA:2*εRef+2*εNbr≤η₀:=by dsimp [εRef];linarith
  have hB:εRef+εNbr≤η₀:=by dsimp [εRef];linarith
  have hC:c*εNbr≤η₀:=by nlinarith [hcoeff]
  refine ⟨εRef,εNbr,hR,hN,hA,hB,hC,?_,?_⟩
  · intro hNbr
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*((hNbr:ℝ)+1))).2
    have hn:0≤(hNbr:ℝ):=Nat.cast_nonneg _
    nlinarith
  · intro n u hun
    have hreal:(u:ℝ)≤n:=by exact_mod_cast hun
    have hU:=mul_le_mul_of_nonneg_left hreal hN.le
    have hAn:=mul_le_mul_of_nonneg_right hA (show (0:ℝ)≤n by positivity)
    have hBn:=mul_le_mul_of_nonneg_right hB (show (0:ℝ)≤n by positivity)
    have hCn:=mul_le_mul_of_nonneg_right hC (show (0:ℝ)≤n by positivity)
    dsimp [c] at hCn
    constructor
    · nlinarith
    constructor <;> nlinarith
end Oberwolfach
