module

public import Oberwolfach.OrdinaryWeightedSelectorCorrectionFailureBudget
public import Oberwolfach.CommonEvents

@[expose] public section
/-! Turn the explicit common-event loss into the original probability target. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_weighted_selector_probability_budget (χ:ℝ) (hχ:0<χ):
    ∃N:ℕ,1 ≤ N ∧ ∀n:ℕ,N ≤ n → 
    ∀εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal:ℝ,
      εE ≤ χ/64 → ζ ≤ χ/64 → χpair ≤ χ/64 → χlist ≤ χ/64 → χbal ≤ χ/64 → χbd ≤ χ/64 → χnbr ≤ χ/64 → χpairR ≤ χ/64 → χpath ≤ χ/64 → 
      χcol ≤ χ/64 → χhub ≤ χ/64 → χglobal ≤ χ/64 → χlocal ≤ χ/64 → 
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω → Prop),
    let loss:=(((((((εE+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath);
    1-loss-χcol-χhub-χglobal-2/(n:ℝ)^10-(1/(n:ℝ)+2/(n:ℝ)^2)-χlocal ≤ μ.probability Event → 
    1-χ-1/(n:ℝ)^10 ≤ μ.probability Event :=by
  obtain ⟨N,hN,hbudget⟩:=ordinary_weighted_selector_correction_failure_budget χ hχ
  refine ⟨N,hN,?_⟩
  intro n hn εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hE hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal Ω _ μ Event loss hprob
  have hb':=hbudget n hn εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hE hζ hp hl hb hbd hnbr hpR hpath (by linarith) (by linarith) (by linarith) (by linarith)
  linarith
end Oberwolfach
