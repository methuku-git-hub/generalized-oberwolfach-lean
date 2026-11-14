module

public import Oberwolfach.OrdinaryOriginalPreSampleJointThresholdsSeparateListsAt

@[expose] public section
/-! The edit and correction rates are fixed first.  Once the common vortex
size and failure allowances are chosen, obtain matching and correction
thresholds for those same rates and for the same terminal interface. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_general_fixed_rates_to_joint_thresholds
    (L rstar d m k dMin:ℕ) (hr:3≤rstar) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs:ℝ)
    (hjoint:OrdinaryOriginalPreSampleFixedJointRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs)
    (hm:7≤m) (hε:0<εvortex) (hεearly:εvortex≤εearly) (habs:εvortex≤εabs) (hv:εvortex≤εv)
    (hEarly:OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin):
    ∀(βv:ℝ) (mv:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ),
      0<ζ→0<χpair→0<χlist→0<χbal→0<χbd→0<χnbr→0<χpairR→0<χpath→
      0<χlocal→0<χglobal→0<χhub→0<χcol→
      OrdinaryOriginalPreSampleJointThresholdsSeparateListsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv
        mv (2*mv) 10 ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol ξedit ξAbs βv :=by
  intro βv mv ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
    hζ hχpair hχlist hχbal hχbd hχnbr hχpairR hχpath hχlocal hχglobal hχhub hχcol
  have hterminal:=ordinary_original_presample_joint_terminal_separate_lists_at L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
    hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs βv
    hjoint hm hθhost hε hεearly hEarly
  exact ordinary_presample_choose_joint_thresholds_separate_lists L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
    hr hβfreq hβ1 hρ₀ hρ1 hα hθhost βPlace lamPlace ζPlace εearly
    εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs βv hterminal hε habs hv
    mv (2*mv) 10 ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
    hζ hχpair hχlist hχbal hχbd hχnbr hχpairR hχpath hχlocal hχglobal hχhub hχcol
end Oberwolfach
