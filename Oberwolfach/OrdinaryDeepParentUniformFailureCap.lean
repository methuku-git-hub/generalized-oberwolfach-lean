module

public import Oberwolfach.OrdinaryWeightedDeepUniformFailureCap

@[expose] public section
/-! Reserve failure budget for the all-level parent and reference events in
addition to the matching, correction and deep events. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_parent_uniform_failure_cap (χ:ℝ) (hχ:0<χ):
    ∃cap:ℝ,0<cap ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal:ℝ,
      ζ≤cap→χpair≤cap→χlist≤cap→χbal≤cap→χbd≤cap→χnbr≤cap→χpairR≤cap→χpath≤cap→
      χcol≤cap→χhub≤cap→χglobal≤cap→χlocal≤cap→
    ∀χinner χdeep χone χtwo χcut χhost χref:ℝ,
      χinner≤cap→χdeep≤cap→χone≤cap→χtwo≤cap→χcut≤cap→χhost≤cap→χref≤cap→
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω→Prop),
    let loss:=(((((((0+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath);
    1-(loss+χcol+χhub+χglobal+χlocal+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+
      χinner+χdeep+χone+χtwo+χcut+χhost+χref)≤μ.probability Event→
    1-χ-1/(n:ℝ)^10≤μ.probability Event :=by
  obtain ⟨c,hc,N,hN,hbase⟩:=ordinary_weighted_deep_uniform_failure_cap χ hχ
  refine ⟨c/2,by positivity,N,hN,?_⟩
  intro n hn ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
    χinner χdeep χone χtwo χcut χhost χref hi hd h1 h2 hcut hhost href Ω _ μ Event loss hprob
  have hc0:0≤c:=hc.le
  have hsum:χhost+χref≤c:=by linarith
  apply hbase n hn (χhost+χref) ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hsum (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    χinner χdeep χone χtwo χcut (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    Ω μ Event
  dsimp only [loss] at hprob
  linarith only [hprob]
end Oberwolfach
