module

public import Oberwolfach.OrdinaryWeightedCorrectionChooseLocalThresholds
public import Oberwolfach.OrdinaryWeightedCorrectionChooseTerminal
public import Oberwolfach.OrdinaryFirstVortexCorrectionChooseThreshold

@[expose] public section
/-! The correction probability callback and first-vortex geometry can be
prepared before choosing a host, its factor family, or the random sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_correction_common_vortex_thresholds
    (r d:ℕ) (hd:2 ≤ d) (mAbs a b t f q₀:ℕ)
    (αcorr pstar ω εabs εv L ξ:ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterAbsorberChoices r d hd mAbs a b αcorr pstar ω εabs εv L ξ)
    (θhost α ρ₀ βfreq ε:ℝ)
    (hθ:(1/2:ℝ) ≤ θhost) (hα:0<α) (hρ:0<ρ₀) (hρ1:ρ₀ ≤ 1)
    (hβ:0<βfreq) (hβ1:βfreq ≤ 1) (hε:0<ε) (habs:ε ≤ εabs) (hv:ε ≤ εv)
    (ζlocal χlocal χglobal χhub χcol C:ℝ)
    (hζ:0<ζlocal) (hlocal:0<χlocal) (hglobal:0<χglobal)
    (hhub:0<χhub) (hcol:0<χcol) (hC:0 ≤ C):
    ∃Ncorr Nc Ng Nh Ncol Ngeom:ℕ,
      1 ≤ Ncorr ∧ 1 ≤ Nc ∧ 1 ≤ Ng ∧ 1 ≤ Nh ∧ 1 ≤ Ncol ∧ 1 ≤ Ngeom ∧
      OrdinaryWeightedCorrectionAfterLocalThresholds r d hd mAbs a b t f q₀ Ncorr Nc Ng Nh Ncol
        αcorr pstar ω εabs εv L ξ ζlocal χlocal χglobal χhub χcol C ∧
      OrdinaryFirstVortexCorrectionThresholdShape Ngeom Nc Ng Nh Ncol θhost α ρ₀ βfreq ε εabs εv :=by
  obtain ⟨Ncorr,hNcorr,hterm⟩:=ordinary_weighted_correction_choose_terminal r d hd mAbs a b
    αcorr pstar ω εabs εv L ξ hcorr t f q₀
  obtain ⟨Nc,Ng,Nh,Ncol,hNc,hNg,hNh,hNcol,hlocal⟩:=
    ordinary_weighted_correction_choose_local_thresholds r d hd mAbs a b t f q₀ Ncorr
      αcorr pstar ω εabs εv L ξ hterm ζlocal χlocal χglobal χhub χcol C
      hζ hlocal hglobal hhub hcol hC
  obtain ⟨Ngeom,hNgeom,hgeom⟩:=ordinary_first_vortex_correction_choose_threshold
    θhost α ρ₀ βfreq ε εabs εv hθ hα hρ hρ1 hβ hβ1 hε habs hv Nc Ng Nh Ncol
  exact ⟨Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hlocal,hgeom⟩
end Oberwolfach
