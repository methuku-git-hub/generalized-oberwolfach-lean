module

public import Oberwolfach.OrdinaryAsymmetricGeometryWithInitialStatic

@[expose] public section
/-! A single early matching coefficient also leaves room in the parent
cleanup budgets for the normalized root-cover and deep-cover losses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_shared_cleanup_parent_margins
    (ζh ζe γ eParent hParent:ℝ)
    (hζh:0<ζh) (hζe:0<ζe) (hγ:0<γ) (he:0<eParent) (hh:0<hParent):
    ∃c:ℝ,0<c ∧ c≤min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2 ∧
    ∀ε N η ell:ℝ,0<ε→0≤N→0≤η→0≤ell→
      η≤c*ε/64→ell≤c*ε/64→
      let θ:=c*ε;let κh:=γ*(1/4:ℝ)*ε;let κinner:=(1/4:ℝ)*ε;
      0<θ ∧ θ≤ζh*κh ∧ θ≤ζe*κinner ∧
      ((eParent/2)*ε)*N+3*max (η*N) (ell*N)≤(eParent*ε)*N ∧
      ((hParent/2)*ε)*N+2*(ell*N)≤(hParent*ε)*N :=by
  let base:=min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2
  let c:=min base (min (4*eParent) (4*hParent))
  have hbase:0<base:=by dsimp [base];positivity
  have hc:0<c:=by dsimp [c];positivity
  have hcbase:c≤base:=min_le_left _ _
  have hce:c≤4*eParent:=(min_le_right base _).trans (min_le_left _ _)
  have hch:c≤4*hParent:=(min_le_right base _).trans (min_le_right _ _)
  have hcbh:c≤ζh*γ*(1/4:ℝ):=by
    have h:=min_le_left (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))
    dsimp [base] at hcbase
    linarith
  have hcbe:c≤ζe*(1/4:ℝ):=by
    have h:=min_le_right (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))
    dsimp [base] at hcbase
    linarith
  refine ⟨c,hc,hcbase,?_⟩
  intro ε N η ell hε hN hη hell hηcap hellcap θ κh κinner
  have hθh:θ≤ζh*κh:=by
    dsimp [θ,κh]
    nlinarith [mul_le_mul_of_nonneg_right hcbh hε.le]
  have hθe:θ≤ζe*κinner:=by
    dsimp [θ,κinner]
    nlinarith [mul_le_mul_of_nonneg_right hcbe hε.le]
  have hm:max η ell≤c*ε/64:=max_le hηcap hellcap
  have heRate:(eParent/2)*ε+3*max η ell≤eParent*ε:=by
    nlinarith [mul_le_mul_of_nonneg_right hce hε.le]
  have hhRate:(hParent/2)*ε+2*ell≤hParent*ε:=by
    nlinarith [mul_le_mul_of_nonneg_right hch hε.le]
  have hmax:max (η*N) (ell*N)≤max η ell*N:=
    max_le (mul_le_mul_of_nonneg_right (le_max_left η ell) hN)
      (mul_le_mul_of_nonneg_right (le_max_right η ell) hN)
  refine ⟨by dsimp [θ];positivity,hθh,hθe,?_,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right heRate hN]
  · nlinarith [mul_le_mul_of_nonneg_right hhRate hN]
end Oberwolfach
