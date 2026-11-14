module

public import Oberwolfach.OrdinaryAsymmetricSampledCoverGeometryHierarchy

@[expose] public section
/-! Choose the matching coefficient after the two pairing tolerances, with
room for the parent profile margins. The cleanup and parent coefficients
are distinct, so their difference pays for the actual fine-cover rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem ordinary_asymmetric_parent_margin_coefficient_choice
    (ζh ζe γ eParent hParent:ℝ)
    (hζh:0<ζh) (hζe:0<ζe) (hγ:0<γ) (heParent:0<eParent) (hhParent:0<hParent):
    ∃cMatch eCleanup hCleanup:ℝ,
      0<cMatch ∧ 0<eCleanup ∧ 0<hCleanup ∧
      eCleanup=eParent/2 ∧ hCleanup=hParent/2 ∧
      cMatch≤min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2 ∧
    ∀ε n ηrate ellrate:ℝ,0≤ε→0≤n→
      ηrate≤cMatch*ε/64→ellrate≤cMatch*ε/64→
      (eCleanup*ε)*n+3*max (ηrate*n) (ellrate*n)≤(eParent*ε)*n ∧
      (hCleanup*ε)*n+2*(ellrate*n)≤(hParent*ε)*n:=by
  let canonical:ℝ:=min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2
  let cMatch:ℝ:=min canonical (min (eParent/10) (hParent/10))
  have hcanonical:0<canonical:=by dsimp [canonical];positivity
  have hc:0<cMatch:=by dsimp [cMatch];positivity
  have hcCanon:cMatch≤canonical:=min_le_left _ _
  have hcE:cMatch≤eParent/10:=(min_le_right _ _).trans (min_le_left _ _)
  have hcH:cMatch≤hParent/10:=(min_le_right _ _).trans (min_le_right _ _)
  have hE:eParent/2+3*cMatch/64≤eParent:=by linarith
  have hH:hParent/2+2*cMatch/64≤hParent:=by linarith
  refine ⟨cMatch,eParent/2,hParent/2,hc,by positivity,by positivity,rfl,rfl,hcCanon,?_⟩
  intro ε n ηrate ellrate hε hn hη hell
  have hη':ηrate*n≤(cMatch*ε/64)*n:=mul_le_mul_of_nonneg_right hη hn
  have hell':ellrate*n≤(cMatch*ε/64)*n:=mul_le_mul_of_nonneg_right hell hn
  have hmax:max (ηrate*n) (ellrate*n)≤(cMatch*ε/64)*n:=max_le hη' hell'
  have hE':=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hε) hn)
  have hH':=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH hε) hn)
  constructor <;> nlinarith only [hmax,hell',hE',hH']
end Oberwolfach
