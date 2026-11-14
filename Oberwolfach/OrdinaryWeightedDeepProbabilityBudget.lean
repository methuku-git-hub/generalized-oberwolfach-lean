module

public import Oberwolfach.OrdinaryWeightedSelectorCorrectionFailureBudget
public import Oberwolfach.CommonEvents

@[expose] public section
/-! The selector, correction, local tests and all-level deep event fit the
original error allowance with its inverse-tenth-power tail. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_weighted_deep_probability_budget (χ:ℝ) (hχ:0<χ):
    ∃N:ℕ,1 ≤ N ∧ ∀n:ℕ,N ≤ n → 
    ∀εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal:ℝ,
      εE ≤ χ/128 → ζ ≤ χ/128 → χpair ≤ χ/128 → χlist ≤ χ/128 → χbal ≤ χ/128 → χbd ≤ χ/128 → χnbr ≤ χ/128 → χpairR ≤ χ/128 → χpath ≤ χ/128 → 
      χcol ≤ χ/128 → χhub ≤ χ/128 → χglobal ≤ χ/128 → χlocal ≤ χ/128 → 
    ∀χinner χdeep χone χtwo χcut:ℝ,
      χinner ≤ χ/10 → χdeep ≤ χ/10 → χone ≤ χ/10 → χtwo ≤ χ/10 → χcut ≤ χ/10 → 
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω → Prop),
    let loss:=(((((((εE+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath);
    1-(loss+χcol+χhub+χglobal+χlocal+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+
      χinner+χdeep+χone+χtwo+χcut) ≤ μ.probability Event → 
    1-χ-1/(n:ℝ)^10 ≤ μ.probability Event :=by
  obtain ⟨N,hN,hbudget⟩:=ordinary_weighted_selector_correction_failure_budget (χ/2) (by positivity)
  refine ⟨N,hN,?_⟩
  intro n hn εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hE hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
    χinner χdeep χone χtwo χcut hi hd h1 h2 hc Ω _ μ Event loss hprob
  have hb':=hbudget n hn εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith
end Oberwolfach
