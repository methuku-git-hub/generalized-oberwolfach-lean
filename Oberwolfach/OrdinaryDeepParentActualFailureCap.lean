module

public import Oberwolfach.OrdinaryDeepParentBalanceFailureBudget

@[expose] public section
/-! Specialize the common event's failure allocation to its actual zero
prior loss, including both the parent and three-step balance events. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_parent_actual_failure_cap (χ:ℝ) (hχ:0<χ):
    ∃cap:ℝ,0<cap ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal:ℝ,
      ζ≤cap→χpair≤cap→χlist≤cap→χbal≤cap→χbd≤cap→χnbr≤cap→χpairR≤cap→χpath≤cap→
      χcol≤cap→χhub≤cap→χglobal≤cap→χlocal≤cap→
    ∀χinner χdeep χone χtwo χcut χhost χref χthree:ℝ,
      χinner≤cap→χdeep≤cap→χone≤cap→χtwo≤cap→χcut≤cap→χhost≤cap→χref≤cap→χthree≤cap→
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω→Prop),
    let loss:=(((((((0+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath);
    1-(loss+χcol+χhub+χglobal+χlocal+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+
      χinner+χdeep+χone+χtwo+χcut)-χhost-χref-χthree≤μ.probability Event→
    1-χ-1/(n:ℝ)^10≤μ.probability Event :=by
  obtain ⟨cap,hcap,N,hN,hbudget⟩:=ordinary_deep_parent_balance_failure_cap χ hχ
  refine ⟨cap,hcap,N,hN,?_⟩
  intro n hn ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
    χinner χdeep χone χtwo χcut χhost χref χthree hi hd h1 h2 hc hhost href hthree Ω _ μ Event loss hprob
  exact hbudget n hn 0 ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hcap.le hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
    χinner χdeep χone χtwo χcut χhost χref χthree hi hd h1 h2 hc hhost href hthree Ω μ Event hprob
end Oberwolfach
