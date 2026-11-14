module

public import Oberwolfach.OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold
public import Oberwolfach.OrdinaryNonrootGeometryStaticLossMono

@[expose] public section
/-! One threshold for all spoke rates in [0,1], obtained by applying the
geometry at rate one and shrinking the deterministic loss budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_sharp_geometry_uniform_spoke_rate
    (mWheel loadK d k:ℕ) (β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout:ℝ)
    (hρ₀:0<ρ₀) (hβ:0≤β) (hξ:0≤ξroot) (hεR:0≤εR) (hεH:0≤εH)
    (hmax:OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh 1 εR εH
      βparent b B εparent gap βout ζout ηpack εout):
    ∃m₀:ℕ,1≤m₀ ∧ ∀pH:ℝ,0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold mWheel loadK d k m₀ β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout :=by
  obtain ⟨m₀,hm₀,hmax⟩:=hmax
  refine ⟨m₀,hm₀,?_⟩
  intro pH hpH hpH1 V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q i hi
    Vloc Uloc I T J W A C Xf Zf deepCost deep cover loss bin cin ell fout binner cross
  have hOld:=hmax V U P D m hreg hn hD hρlo hρhi hm Q i hi
  let deepMax:ℝ:=(initialIndexDensity U D*1)*β*T.card+εR*T.card+2*(εH*W.card)+
      3*(2*((3*d:ℕ):ℝ))+2*deepCost
  change (T.card:ℝ)+W.card≤lam*Fintype.card Vloc ∧
    (T.card:ℝ)≤(βe/4)*Fintype.card (Vloc⊕Uloc) ∧
    (W.card:ℝ)≤(βh/2)*Fintype.card (Vloc⊕Uloc) ∧
    0≤deepMax ∧ 0≤bin ∧ 0≤cin ∧
    OrdinaryNonrootGeometryStatic (mWheel+1) k (ρ₀/16) βparent βout b B εparent (εparent+gap)
      ηpack ξreserve ζout p εout (deepMax+2*cover) (bin+deepMax+4*cover) (cin+deepMax+loss) Xf Zf ∧
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card A ∧
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card C at hOld
  obtain ⟨hT,hTcap,hWcap,hdeepMax,hbin,hcin,hstatic,hscaleA,hscaleC⟩:=hOld
  have hρ:0 ≤ initialIndexDensity U D:=hρ₀.le.trans hρlo
  have hq:initialIndexDensity U D*pH ≤ initialIndexDensity U D*1:=mul_le_mul_of_nonneg_left hpH1 hρ
  have hprod:initialIndexDensity U D*pH*β*(T.card:ℝ) ≤ initialIndexDensity U D*1*β*(T.card:ℝ):=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq hβ) (by positivity)
  have hdeep:deep≤deepMax:=by dsimp [deep,deepMax]; linarith only [hprod]
  have hdeepCost:0≤deepCost:=ordinary_fine_deep_cost_nonneg Q ξroot hξ i
  have hdeep0:0≤deep:=by dsimp [deep]; positivity
  have hf:fout≤deepMax+2*cover:=by dsimp [fout]; linarith
  have hbinner:binner≤bin+deepMax+4*cover:=by dsimp [binner]; linarith
  have hcross:cross≤cin+deepMax+loss:=by dsimp [cross]; linarith
  have hnew:=ordinary_nonroot_geometry_static_loss_mono (mWheel+1) k (ρ₀/16) βparent βout b B εparent (εparent+gap)
    ηpack ξreserve ζout p εout (deepMax+2*cover) (bin+deepMax+4*cover) (cin+deepMax+loss) fout binner cross Xf Zf hstatic hf hbinner hcross
  exact ⟨hT,hTcap,hWcap,hdeep0,hbin,hcin,hnew,hscaleA,hscaleC⟩
end Oberwolfach
