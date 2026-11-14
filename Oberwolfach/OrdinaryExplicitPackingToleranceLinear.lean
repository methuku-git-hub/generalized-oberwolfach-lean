module

public import Oberwolfach.OrdinaryNearBalancePackingExplicit

@[expose] public section
/-! The explicit packing tolerance admits a linear lower bound in the
requested cleanup tolerance, with the other constants chosen first. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def ordinaryPackingLinearConstant (h β cStar:ℝ) (r:ℕ):ℝ :=
  min (h/100) (min (β/160) (min (β/(100*(r:ℝ)^4)) (min cStar (1/20))))

theorem ordinary_explicit_packing_tolerance_linear
    (r:ℕ) (hr:0<r) (δ ω h β cStar γ:ℝ)
    (hδ:0<δ) (hω:0<ω) (hh:0<h) (hβ:0<β) (hc:0<cStar)
    (hγ:0≤γ) (hγone:γ≤1):
    let c:=ordinaryPackingLinearConstant h β cStar r
    let ξ:=min (min (h/100) (γ/20))
      (min (β/160) (min (β/(100*(r:ℝ)^4)) cStar));
    0<c ∧ (δ*ω*c/1000)*γ≤δ*ω*ξ/1000 :=by
  let c:=ordinaryPackingLinearConstant h β cStar r
  have hrR:0<(r:ℝ):=by exact_mod_cast hr
  have hcpos:0<c:=by dsimp [c,ordinaryPackingLinearConstant];positivity
  have hcH:c≤h/100:=min_le_left _ _
  have hcB:c≤β/160:=(min_le_right _ _).trans (min_le_left _ _)
  have hcT:c≤β/(100*(r:ℝ)^4):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcC:c≤cStar:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc20:c≤1/20:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hbound:∀a:ℝ,0≤a→c≤a→γ*c≤a:=by
    intro a ha hca
    have hmul:=mul_le_mul_of_nonneg_left hca hγ
    have hgap:=mul_nonneg (sub_nonneg.mpr hγone) ha
    nlinarith only [hmul,hgap]
  have hξ:γ*c≤min (min (h/100) (γ/20))
      (min (β/160) (min (β/(100*(r:ℝ)^4)) cStar)):=by
    refine le_min (le_min (hbound _ (by positivity) hcH) ?_) (le_min (hbound _ (by positivity) hcB) (le_min (hbound _ (by positivity) hcT) (hbound _ hc.le hcC)))
    have hm:=mul_le_mul_of_nonneg_left hc20 hγ
    nlinarith only [hm]
  have hm:=mul_le_mul_of_nonneg_left hξ (show 0≤δ*ω/1000 by positivity)
  refine ⟨hcpos,?_⟩
  nlinarith only [hm]
end Oberwolfach
