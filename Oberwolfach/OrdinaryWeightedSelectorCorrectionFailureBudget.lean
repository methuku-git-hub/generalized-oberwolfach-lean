module

public import Oberwolfach.OrdinaryCombinedOriginalFailureBudget

@[expose] public section
/-! The selector and both local correction tests fit the original failure
allowance, retaining its inverse-tenth-power tail. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_weighted_selector_correction_failure_budget (χ:ℝ) (hχ:0<χ):
    ∃N:ℕ,1 ≤ N ∧ ∀n:ℕ,N ≤ n → 
    ∀εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal:ℝ,
      εE ≤ χ/64 → ζ ≤ χ/64 → χpair ≤ χ/64 → χlist ≤ χ/64 → χbal ≤ χ/64 → χbd ≤ χ/64 → χnbr ≤ χ/64 → χpairR ≤ χ/64 → χpath ≤ χ/64 → 
      χcol ≤ χ/8 → χhub ≤ χ/8 → χglobal ≤ χ/8 → χlocal ≤ χ/8 → 
      (((((((εE+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath)+
        χcol+χhub+χglobal+χlocal+
        (2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)) ≤ χ+1/(n:ℝ)^10 :=by
  obtain ⟨N,hN,hbudget⟩:=ordinary_combined_original_failure_budget (χ/2) (by positivity)
  refine ⟨N,hN,?_⟩
  intro n hn εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hE hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
  have hb':=hbudget n hn εE ζ χpair χlist χbal χbd χnbr χpairR χpath
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith
end Oberwolfach
