module

public import Oberwolfach.OrdinaryDeepParentActualFailureCap

@[expose] public section
/-! The triangle parent event can retain both the original hub event and a
separately attached inner-scale hub event, as well as the balance event,
within the original final failure allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_parent_inner_balance_failure_cap (χ:ℝ) (hχ:0<χ):
    ∃cap:ℝ,0<cap ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal:ℝ,
      ζ≤cap→χpair≤cap→χlist≤cap→χbal≤cap→χbd≤cap→χnbr≤cap→χpairR≤cap→χpath≤cap→
      χcol≤cap→χhub≤cap→χglobal≤cap→χlocal≤cap→
    ∀χinner χdeep χone χtwo χcut χhost χref χthree χtriangleHub:ℝ,
      χinner≤cap→χdeep≤cap→χone≤cap→χtwo≤cap→χcut≤cap→χhost≤cap→χref≤cap→χthree≤cap→χtriangleHub≤cap→
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω→Prop),
    let loss:=(((((((0+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath);
    1-(loss+χcol+χhub+χglobal+χlocal+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+
      χinner+χdeep+χone+χtwo+χcut)-χhost-χref-χthree-χtriangleHub≤μ.probability Event→
    1-χ-1/(n:ℝ)^10≤μ.probability Event :=by
  obtain ⟨cap0,hcap0,N,hN,hbudget⟩:=ordinary_deep_parent_actual_failure_cap χ hχ
  refine ⟨cap0/2,by positivity,N,hN,?_⟩
  intro n hn ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
    χinner χdeep χone χtwo χcut χhost χref χthree χtriangleHub hi hd h1 h2 hc hhost href hthree htriangle Ω _ μ Event loss hprob
  have hcap:cap0/2≤cap0:=by linarith
  have hsum:χthree+χtriangleHub≤cap0:=by linarith
  apply hbudget n hn ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
    (hζ.trans hcap) (hp.trans hcap) (hl.trans hcap) (hb.trans hcap) (hbd.trans hcap) (hnbr.trans hcap)
    (hpR.trans hcap) (hpath.trans hcap) (hcol.trans hcap) (hhub.trans hcap) (hglobal.trans hcap) (hlocal.trans hcap)
    χinner χdeep χone χtwo χcut χhost χref (χthree+χtriangleHub)
    (hi.trans hcap) (hd.trans hcap) (h1.trans hcap) (h2.trans hcap) (hc.trans hcap)
    (hhost.trans hcap) (href.trans hcap) hsum Ω μ Event
  linarith only [hprob]
end Oberwolfach
