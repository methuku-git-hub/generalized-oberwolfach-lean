module

public import Oberwolfach.FirstVortexActualParentAlignedRates
public import Oberwolfach.SuccessorWeightParameterMono

@[expose] public section
/-! A parent event valid for a larger weight upper bound remains valid when
its selected weights have the smaller upper bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_parent_aligned_weight_monotonicity
    (r:ℕ) (ρ₀ sstar tstar Bsmall Bbig δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff:ℝ)
    (hρ:0<ρ₀) (hs:0<sstar) (he:0<ε) (hBsmall:0≤Bsmall) (hB:Bsmall≤Bbig)
    (h:FirstVortexActualParentAlignedRates r ρ₀ sstar tstar Bbig δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff):
    FirstVortexActualParentAlignedRates r ρ₀ sstar tstar Bsmall δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff :=by
  let m:ℝ:=((r+4):ℕ)
  let ps:=ρ₀*sstar/(2*m)
  have hm:0<m:=by dsimp [m]; positivity
  have hps:0<ps:=by dsimp [ps]; positivity
  have hCp:11*(m+1)^4*(2*Bsmall/ps^(2*(r+4)+1))≤11*(m+1)^4*(2*Bbig/ps^(2*(r+4)+1)):=by
    gcongr
  have hCl:5*(m+1)^4*(2*Bsmall/ps^(2*(r+4)+1))≤5*(m+1)^4*(2*Bbig/ps^(2*(r+4)+1)):=by
    gcongr
  dsimp only [FirstVortexActualParentAlignedRates] at h ⊢
  obtain ⟨δ',εBal,ζBal,hδ,hδle,hcfg,hκ,href,hendpoint,hparent,hdeep,hactive,hrow,hspoke,heBal,hζBal,hecap,hζcap,hbalance,hmargin,hcycle,hpath⟩:=h
  refine ⟨δ',εBal,ζBal,hδ,hδle,hcfg,hκ,href,hendpoint,?_,?_,?_,hrow,hspoke,heBal,hζBal,hecap,hζcap,hbalance,hmargin,hcycle,hpath⟩
  · have hh:=mul_nonneg (sub_nonneg.mpr hCp) hδ.le
    dsimp only [m,ps] at hh
    nlinarith
  · have hh:=mul_nonneg (sub_nonneg.mpr hCp) hδ.le
    dsimp only [m,ps] at hh
    nlinarith
  · have hh:=mul_nonneg (mul_nonneg (sub_nonneg.mpr hCl) (by positivity : 0≤4/ε)) hδ.le
    dsimp only [m,ps] at hh
    nlinarith
end Oberwolfach
