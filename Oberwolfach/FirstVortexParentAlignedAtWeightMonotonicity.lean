module

public import Oberwolfach.FirstVortexActualParentAlignedAt
public import Oberwolfach.FirstVortexActualParentAlignedWitness
public import Oberwolfach.FirstVortexParentAlignedWeightMonotonicity

@[expose] public section
/-! Preserve the already selected parent and balance witnesses when the
actual parent weights have a smaller upper bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_parent_aligned_at_weight_monotonicity
    (r:ℕ) (ρ₀ sstar tstar Bsmall Bbig δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff δ' εBal ζBal:ℝ)
    (hρ:0<ρ₀) (hs:0<sstar) (he:0<ε) (hBsmall:0≤Bsmall) (hB:Bsmall≤Bbig)
    (h:FirstVortexActualParentAlignedAt r ρ₀ sstar tstar Bbig δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff δ' εBal ζBal):
    FirstVortexActualParentAlignedAt r ρ₀ sstar tstar Bsmall δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff δ' εBal ζBal :=by
  let m:ℝ:=((r+4):ℕ)
  let ps:=ρ₀*sstar/(2*m)
  have hm:0<m:=by dsimp [m];positivity
  have hps:0<ps:=by dsimp [ps];positivity
  have hCp:11*(m+1)^4*(2*Bsmall/ps^(2*(r+4)+1))≤11*(m+1)^4*(2*Bbig/ps^(2*(r+4)+1)):=by gcongr
  have hCl:5*(m+1)^4*(2*Bsmall/ps^(2*(r+4)+1))≤5*(m+1)^4*(2*Bbig/ps^(2*(r+4)+1)):=by gcongr
  dsimp only [FirstVortexActualParentAlignedAt] at h ⊢
  obtain ⟨hδ,hδle,hcfg,hκ,href,hendpoint,hparent,hdeep,hactive,hrow,hspoke,heBal,hζBal,hecap,hζcap,hbalance,hmargin,hcycle,hpath⟩:=h
  refine ⟨hδ,hδle,hcfg,hκ,href,hendpoint,?_,?_,?_,hrow,hspoke,heBal,hζBal,hecap,hζcap,hbalance,hmargin,hcycle,hpath⟩
  · have hh:=mul_nonneg (sub_nonneg.mpr hCp) hδ.le
    dsimp only [m,ps] at hh
    nlinarith
  · have hh:=mul_nonneg (sub_nonneg.mpr hCp) hδ.le
    dsimp only [m,ps] at hh
    nlinarith
  · have hh:=mul_nonneg (mul_nonneg (sub_nonneg.mpr hCl) (by positivity : 0≤4/ε)) hδ.le
    dsimp only [m,ps] at hh
    nlinarith

/-- The already selected witness may be used with any dominating base tolerance. -/
theorem first_vortex_parent_aligned_witness_to_at
    (r:ℕ) (ρ₀ sstar tstar B δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff δ' εBal ζBal:ℝ)
    (hδle:δ'≤δ)
    (h:FirstVortexActualParentAlignedWitness r ρ₀ sstar tstar B ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff δ' εBal ζBal):
    FirstVortexActualParentAlignedAt r ρ₀ sstar tstar B δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff δ' εBal ζBal :=by
  dsimp only [FirstVortexActualParentAlignedWitness] at h
  dsimp only [FirstVortexActualParentAlignedAt]
  exact ⟨h.1,hδle,h.2⟩
end Oberwolfach
