module

public import Oberwolfach.OrdinaryTriangleParentEndpointFailureCap

@[expose] public section
/-! The failure accounting for the original assigned parent witness and the
attached inner and endpoint events uses each loss exactly once. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_assigned_endpoint_failure_budget (χ:ℝ) (hχ:0<χ):
    ∃cap:ℝ,0<cap ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal:ℝ,
      ζ≤cap→χpair≤cap→χlist≤cap→χbal≤cap→χbd≤cap→χnbr≤cap→χpairR≤cap→χpath≤cap→
      χcol≤cap→χhub≤cap→χglobal≤cap→χlocal≤cap→
    ∀χinner χdeep χone χtwo χcut χhost χref χHub χendpoint:ℝ,
      χinner≤cap→χdeep≤cap→χone≤cap→χtwo≤cap→χcut≤cap→χhost≤cap→χref≤cap→χHub≤cap→χendpoint≤cap→
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω→Prop),
    let loss0:=(((((((0+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath);
    let loss:=loss0+χcol+χhub+χglobal+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+χlocal;
    1-(loss+χdeep+χone+χtwo+χcut+χHub+χhost+χref)-χinner-χendpoint≤μ.probability Event→
    1-χ-1/(n:ℝ)^10≤μ.probability Event :=by
  obtain ⟨cap,hcap,N,hN,hbudget⟩:=ordinary_triangle_parent_endpoint_failure_cap χ hχ
  refine ⟨cap,hcap,N,hN,?_⟩
  intro n hn ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
    χinner χdeep χone χtwo χcut χhost χref χHub χendpoint
    hi hd h1 h2 hc hhost href hHub hend Ω _ μ Event loss0 loss hprob
  apply hbudget n hn ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
    χinner χdeep χone χtwo χcut χhost χref 0 χHub χendpoint
    hi hd h1 h2 hc hhost href hcap.le hHub hend Ω μ Event
  dsimp [loss,loss0] at hprob ⊢
  linarith only [hprob]
end Oberwolfach
