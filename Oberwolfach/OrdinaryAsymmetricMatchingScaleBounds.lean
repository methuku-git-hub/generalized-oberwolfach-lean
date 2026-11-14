module

public import Oberwolfach.OrdinaryGeneralAsymmetricMarginsFromCapacity

@[expose] public section
/-! Convert fixed relative hub and endpoint tolerances into a matching
capacity linear in the vortex scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_matching_scale_bounds
    (ζh ζe γ α ε n innerA innerPhysical eCoeff:ℝ)
    (hζh:0<ζh) (hζe:0<ζe) (hγ:0<γ) (hα:0<α) (hε:0<ε) (hn:0≤n)
    (hAlo:α*ε*n≤ innerA) (hAhi:innerA≤ε*n) (hinside:innerA≤ innerPhysical)
    (he:γ≤eCoeff):
    let κh:=γ*α*ε;
    let κinner:=α*ε;
    let c:=min (ζh*γ*α) (ζe*α)/2;
    let θmatch:=c*ε;
    0<κh ∧ 0<κinner ∧ 0<c ∧ 0<θmatch ∧
    κh*n≤γ*innerA ∧ κinner*n≤ innerPhysical ∧
    θmatch≤ζh*κh ∧ θmatch≤ζe*κinner ∧ γ*innerA≤(eCoeff*ε)*n:=by
  intro κh κinner c θmatch
  have hκh:0<κh:=by dsimp [κh];positivity
  have hκi:0<κinner:=by dsimp [κinner];positivity
  have hc:0<c:=by dsimp [c];positivity
  have hθ:0<θmatch:=by dsimp [θmatch];positivity
  have hlo:=mul_le_mul_of_nonneg_left hAlo hγ.le
  have hhi:=mul_le_mul_of_nonneg_left hAhi hγ.le
  have he':=mul_le_mul_of_nonneg_right he (mul_nonneg hε.le hn)
  have hc1:c≤ζh*γ*α:=by
    have hh:=min_le_left (ζh*γ*α) (ζe*α)
    dsimp [c]
    nlinarith [mul_nonneg (mul_nonneg hζh.le hγ.le) hα.le]
  have hc2:c≤ζe*α:=by
    have hh:=min_le_right (ζh*γ*α) (ζe*α)
    dsimp [c]
    nlinarith [mul_nonneg hζe.le hα.le]
  have ht1:=mul_le_mul_of_nonneg_right hc1 hε.le
  have ht2:=mul_le_mul_of_nonneg_right hc2 hε.le
  refine ⟨hκh,hκi,hc,hθ,?_,?_,?_,?_,?_⟩
  · dsimp [κh]
    nlinarith only [hlo]
  · dsimp [κinner]
    exact hAlo.trans hinside
  · dsimp [θmatch,κh]
    nlinarith only [ht1]
  · dsimp [θmatch,κinner]
    nlinarith only [ht2]
  · nlinarith only [hhi,he']
end Oberwolfach
