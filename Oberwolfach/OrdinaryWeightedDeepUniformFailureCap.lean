module

public import Oberwolfach.OrdinaryWeightedDeepProbabilityBudget

@[expose] public section
/-! A single positive cap is selected before the individual common-event
failure parameters and before the sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_weighted_deep_uniform_failure_cap (χ:ℝ) (hχ:0<χ):
    ∃cap:ℝ,0<cap ∧ ∃N:ℕ,1 ≤ N ∧ ∀n:ℕ,N ≤ n → 
    ∀εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal:ℝ,
      εE ≤ cap → ζ ≤ cap → χpair ≤ cap → χlist ≤ cap → χbal ≤ cap → χbd ≤ cap → χnbr ≤ cap → χpairR ≤ cap → χpath ≤ cap → 
      χcol ≤ cap → χhub ≤ cap → χglobal ≤ cap → χlocal ≤ cap → 
    ∀χinner χdeep χone χtwo χcut:ℝ,
      χinner ≤ cap → χdeep ≤ cap → χone ≤ cap → χtwo ≤ cap → χcut ≤ cap → 
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω → Prop),
    let loss:=(((((((εE+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath);
    1-(loss+χcol+χhub+χglobal+χlocal+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+
      χinner+χdeep+χone+χtwo+χcut) ≤ μ.probability Event → 
    1-χ-1/(n:ℝ)^10 ≤ μ.probability Event :=by
  obtain ⟨N,hN,hbudget⟩:=ordinary_weighted_deep_probability_budget χ hχ
  refine ⟨χ/256,by positivity,N,hN,?_⟩
  intro n hn εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hE hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
    χinner χdeep χone χtwo χcut hi hd h1 h2 hc Ω _ μ Event loss hprob
  exact hbudget n hn εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
    χinner χdeep χone χtwo χcut (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    Ω μ Event hprob
end Oberwolfach
