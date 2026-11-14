module

public import Oberwolfach.OrdinaryOriginalThresholdChooseFactorThreshold
public import Oberwolfach.OrdinaryCorrectionCommonVortexThresholds

@[expose] public section
/-! Choose compatible matching, correction and first-vortex thresholds
before the factor family and the common sample are chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_matching_correction_common_thresholds
    (rstar m k d K:ℕ) (hd:2 ≤ d)
    (βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel smin τ tMatch ξMatch bMatch:ℝ)
    (BO:Fin K → ℝ)
    (hchoice:OrdinaryOriginalThresholdAfterMatchChoice rstar m k d K hd βfreq ρ₀ α θ θhost
      lam aRow γ cap lamList ζDel smin τ tMatch ξMatch bMatch BO)
    (ζ χpair χlist σ χbal χbd χnbr χpairR χpath:ℝ)
    (hζ:0<ζ) (hχpair:0<χpair) (hχlist:0<χlist) (hσ:0<σ) (hχbal:0<χbal)
    (hχbd:0<χbd) (hχnbr:0<χnbr) (hχpairR:0<χpairR) (hχpath:0<χpath)
    (mAbs aAbs bAbs t f q₀:ℕ) (αcorr pstar ω εabs εv L ξAbs ε:ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterAbsorberChoices rstar d hd mAbs aAbs bAbs
      αcorr pstar ω εabs εv L ξAbs)
    (hθ:(1/2:ℝ) ≤ θhost) (hα:0<α) (hρ:0<ρ₀) (hρ1:ρ₀ ≤ 1)
    (hβ:0<βfreq) (hβ1:βfreq ≤ 1) (hε:0<ε) (habs:ε ≤ εabs) (hv:ε ≤ εv)
    (ζlocal χlocal χglobal χhub χcol C:ℝ)
    (hζlocal:0<ζlocal) (hlocal:0<χlocal) (hglobal:0<χglobal)
    (hhub:0<χhub) (hcol:0<χcol) (hC:0 ≤ C):
    ∃aEvent:ℝ,0<aEvent ∧ ∃Nsel Ncorr Nc Ng Nh Ncol Ngeom:ℕ,
      1 ≤ Ncorr ∧ 1 ≤ Nc ∧ 1 ≤ Ng ∧ 1 ≤ Nh ∧ 1 ≤ Ncol ∧ 1 ≤ Ngeom ∧
      OrdinaryOriginalThresholdForAllFactors rstar m k d K hd Nsel βfreq ρ₀ α θ θhost
        lam aRow γ cap lamList ζDel smin τ tMatch ξMatch bMatch BO
        ζ χpair χlist σ χbal χbd χnbr χpairR χpath aEvent ∧
      OrdinaryWeightedCorrectionAfterLocalThresholds rstar d hd mAbs aAbs bAbs t f q₀ Ncorr Nc Ng Nh Ncol
        αcorr pstar ω εabs εv L ξAbs ζlocal χlocal χglobal χhub χcol C ∧
      OrdinaryFirstVortexCorrectionThresholdShape Ngeom Nc Ng Nh Ncol θhost α ρ₀ βfreq ε εabs εv :=by
  have hsel:=ordinary_original_threshold_choose_losses rstar m k d K hd βfreq ρ₀ α θ θhost
    lam aRow γ cap lamList ζDel smin τ tMatch ξMatch bMatch BO hchoice
    ζ χpair χlist σ χbal χbd χnbr χpairR χpath hζ hχpair hχlist hσ hχbal hχbd hχnbr hχpairR hχpath
  obtain ⟨aEvent,ha,Nsel,hsel⟩:=ordinary_original_threshold_choose_factor_threshold
    rstar m k d K hd βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel smin τ tMatch ξMatch bMatch BO
    ζ χpair χlist σ χbal χbd χnbr χpairR χpath hsel
  obtain ⟨Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hcorr,hgeom⟩:=
    ordinary_correction_common_vortex_thresholds rstar d hd mAbs aAbs bAbs t f q₀
      αcorr pstar ω εabs εv L ξAbs hcorr θhost α ρ₀ βfreq ε
      hθ hα hρ hρ1 hβ hβ1 hε habs hv ζlocal χlocal χglobal χhub χcol C
      hζlocal hlocal hglobal hhub hcol hC
  exact ⟨aEvent,ha,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hcorr,hgeom⟩
end Oberwolfach
