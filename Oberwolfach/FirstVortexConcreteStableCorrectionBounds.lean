module

public import Oberwolfach.FirstVortexSelectorConcreteCorrectionBudgets

@[expose] public section
/-! The concrete selector bounds at a cap below the stable-event cap give
both robust-absorber hypotheses and the row/column correction budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_concrete_stable_correction_bounds
    (n:ℕ) (cap capStable loss δglobal θ err ηphys ηdel ηtype:ℝ)
    (hcap0:0≤cap) (hcap:cap≤capStable)
    (hglobal:ηphys+ηdel+ηtype≤cap*n)
    (hrow:2*(loss+(δglobal*n+(Real.sqrt δglobal*n+1)))+(err+2*(ηphys+ηdel+ηtype))≤(min cap (1:ℝ)/2)*n)
    (hcol:2*(loss+10*θ*n)+err≤(min cap (1:ℝ)/2)*n):
    ηphys+ηdel+ηtype≤capStable*n ∧ min cap (1:ℝ)/2≤capStable ∧
    2*(loss+(δglobal*n+(Real.sqrt δglobal*n+1)))+(err+2*(ηphys+ηdel+ηtype))≤(min cap (1:ℝ)/2)*n ∧
    2*(loss+10*θ*n)+err≤(min cap (1:ℝ)/2)*n :=by
  have hn:0≤(n:ℝ):=by positivity
  have hglobal':cap*n≤capStable*n:=mul_le_mul_of_nonneg_right hcap hn
  have hmin:min cap (1:ℝ)/2≤cap:=by
    have hc:=min_le_left cap (1:ℝ)
    linarith
  exact ⟨hglobal.trans hglobal',hmin.trans hcap,hrow,hcol⟩
end Oberwolfach
