module

public import Oberwolfach.FiniteHighEventsCommon
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section
/-! The numerical margins used in the prescribed-image greedy embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem prescribed_embedding_numerical_margins (β δ n:ℝ)
    (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hroot:Real.sqrt δ≤β/100)
    (hn:2/Real.sqrt δ≤n):
    let t:=Real.sqrt δ*n;
    2≤t ∧ 3*δ*n+2*t+2≤8*t ∧ 2*δ*n+2*t+2≤5*t ∧
    0<β*n-t-δ*n-16*t := by
  intro t
  have hr0:0<Real.sqrt δ:=Real.sqrt_pos.2 hδ
  have hr1:Real.sqrt δ≤1:=by linarith
  have hsq:(Real.sqrt δ)^2=δ:=Real.sq_sqrt hδ.le
  have hn0:0<n:=by
    have hh:(0:ℝ)<2/Real.sqrt δ:=by positivity
    linarith
  have ht:2≤t:=by
    dsimp [t]
    have hh:2≤n*Real.sqrt δ:=(div_le_iff₀ hr0).mp hn
    nlinarith
  have hδroot:δ≤Real.sqrt δ:=by nlinarith
  have hδn:δ*n≤t:=by
    dsimp [t]
    exact mul_le_mul_of_nonneg_right hδroot hn0.le
  have hsmall:17*Real.sqrt δ+δ<β:=by nlinarith [hδroot]
  have hsmalln:17*(Real.sqrt δ*n)+δ*n<β*n:=by
    have hh:=mul_lt_mul_of_pos_right hsmall hn0
    nlinarith
  refine ⟨ht,?_,?_,?_⟩ <;> dsimp [t] at * <;> nlinarith
theorem prescribed_embedding_margins_from_hypotheses (β δ n:ℝ)
    (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hn:2/Real.sqrt δ≤n):
    let t:=Real.sqrt δ*n;
    2≤t ∧ 3*δ*n+2*t+2≤8*t ∧ 2*δ*n+2*t+2≤5*t ∧
    0<β*n-t-δ*n-16*t := by
  apply prescribed_embedding_numerical_margins β δ n hβ hβ1 hδ
  · exact Real.sqrt_le_iff.mpr ⟨by positivity,hδbound⟩
  · exact hn
theorem prescribed_embedding_greedy_slack (β δ n:ℝ)
    (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤n):
    0<β*n-Real.sqrt δ*n-δ*n-16*(Real.sqrt δ*n)-2 := by
  have hr0:0≤Real.sqrt δ:=Real.sqrt_nonneg _
  have hr:Real.sqrt δ≤β/100:=Real.sqrt_le_iff.mpr ⟨by positivity,hδbound⟩
  have hr1:Real.sqrt δ≤1:=by linarith
  have hsq:(Real.sqrt δ)^2=δ:=Real.sq_sqrt hδ.le
  have hδroot:δ≤Real.sqrt δ:=by nlinarith
  have hn0:0≤n:=by
    have hh:(0:ℝ)≤100/β:=by positivity
    linarith
  have hβn:100≤n*β:=(div_le_iff₀ hβ).mp hnβ
  have hcoeff:17*Real.sqrt δ+δ≤(18/100:ℝ)*β:=by linarith
  have hh:=mul_le_mul_of_nonneg_right hcoeff hn0
  nlinarith
end Oberwolfach
