module

public import Oberwolfach.OrdinaryWeightedDeepUniformFailureCap

@[expose] public section
/-! The original failure allowance also covers the parent host, reference
cuts and the same-sample three-step balance event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_parent_balance_failure_cap (χ:ℝ) (hχ:0<χ):
    ∃cap:ℝ,0<cap ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal:ℝ,
      εE≤cap→ζ≤cap→χpair≤cap→χlist≤cap→χbal≤cap→χbd≤cap→χnbr≤cap→χpairR≤cap→χpath≤cap→
      χcol≤cap→χhub≤cap→χglobal≤cap→χlocal≤cap→
    ∀χinner χdeep χone χtwo χcut χhost χref χthree:ℝ,
      χinner≤cap→χdeep≤cap→χone≤cap→χtwo≤cap→χcut≤cap→χhost≤cap→χref≤cap→χthree≤cap→
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω→Prop),
    let loss:=(((((((εE+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath);
    1-(loss+χcol+χhub+χglobal+χlocal+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+
      χinner+χdeep+χone+χtwo+χcut)-χhost-χref-χthree≤μ.probability Event→
    1-χ-1/(n:ℝ)^10≤μ.probability Event :=by
  obtain ⟨cap₀,hcap₀,N,hN,hbudget⟩:=ordinary_weighted_deep_uniform_failure_cap χ hχ
  let cap:=cap₀/4
  have hcap:0<cap:=by dsimp [cap]; positivity
  have hcaple:cap≤cap₀:=by dsimp [cap]; linarith
  refine ⟨cap,hcap,N,hN,?_⟩
  intro n hn εE ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hE hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
    χinner χdeep χone χtwo χcut χhost χref χthree hi hd h1 h2 hc hhost href hthree Ω _ μ Event loss hprob
  have hE':εE+χhost+χref+χthree≤cap₀:=by dsimp [cap] at *; linarith
  have hprob':1-((((((((εE+χhost+χref+χthree)+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath+
      χcol+χhub+χglobal+χlocal+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+χinner+χdeep+χone+χtwo+χcut)≤μ.probability Event:=by
    dsimp [loss] at hprob; linarith only [hprob]
  exact hbudget n hn (εE+χhost+χref+χthree) ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hE' (hζ.trans hcaple) (hp.trans hcaple) (hl.trans hcaple) (hb.trans hcaple) (hbd.trans hcaple)
    (hnbr.trans hcaple) (hpR.trans hcaple) (hpath.trans hcaple) (hcol.trans hcaple) (hhub.trans hcaple)
    (hglobal.trans hcaple) (hlocal.trans hcaple) χinner χdeep χone χtwo χcut
    (hi.trans hcaple) (hd.trans hcaple) (h1.trans hcaple) (h2.trans hcaple) (hc.trans hcaple) Ω μ Event hprob'
end Oberwolfach
