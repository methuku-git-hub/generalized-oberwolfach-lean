module

public import Oberwolfach.PrescribedEmbeddingNumerics

@[expose] public section
/-! An explicit margin for the one-prescribed-vertex cycle case. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem prescribed_embedding_cycle_slack (β δ n:ℝ)
    (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤n):
    0<β*n-Real.sqrt δ*n-δ*n-16*(Real.sqrt δ*n)-4 := by
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

theorem prescribed_embedding_cycle_budget (β δ n M b ℓ:ℝ)
    (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤n)
    (hsize:b+ℓ≤Real.sqrt δ*n+δ*n+1)
    (hM:M≤8*Real.sqrt δ*n):
    b+ℓ+2+2*M<β*n := by
  have hs:=prescribed_embedding_cycle_slack β δ n hβ hβ1 hδ hδbound hnβ
  linarith
end Oberwolfach
