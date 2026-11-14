module

public import Oberwolfach.OrdinaryLocalEndpointSizesFromCleanup
public import Oberwolfach.OrdinaryPhysicalInnerEndpointDomain

@[expose] public section
/-! Fixed lower bounds for the sampling means give positive endpoint-size
and error margins on the inner physical scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_endpoint_mean_margins (p₀ κ:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (hκ:0<κ) (hκ1:κ≤1):
    ∃a δ:ℝ,0<a ∧ a≤1 ∧ 0<δ ∧
    ∀(A B pR pH density eR eH:ℝ),0≤A→κ*A≤B→B≤A→
      p₀≤pR→p₀≤pH→(1/2:ℝ)≤density→
      eR≤δ*A→eH≤δ*A→
      a*(A+B)+eR≤pR*density*A ∧ a*(A+B)+eH≤pH*B:=by
  let a:ℝ:=min (p₀/16) (p₀*κ/8)
  let δ:ℝ:=min (p₀/4) (p₀*κ/2)
  have ha:0<a:=lt_min (by positivity) (by positivity)
  have ha1:a≤1:=by
    have hh:=min_le_left (p₀/16) (p₀*κ/8)
    dsimp [a]
    linarith
  have hδ:0<δ:=lt_min (by positivity) (by positivity)
  refine ⟨a,δ,ha,ha1,hδ,?_⟩
  intro A B pR pH density eR eH hA hBA hBA' hpR hpH hd heR heH
  have haR:a≤p₀/16:=min_le_left _ _
  have haH:a≤p₀*κ/8:=min_le_right _ _
  have hdR:δ≤p₀/4:=min_le_left _ _
  have hdH:δ≤p₀*κ/2:=min_le_right _ _
  have hB:0≤B:=le_trans (mul_nonneg hκ.le hA) hBA
  have hsum:0≤A+B:=add_nonneg hA hB
  have haR':a*(A+B)≤(p₀/16)*(A+B):=mul_le_mul_of_nonneg_right haR hsum
  have haH':a*(A+B)≤(p₀*κ/8)*(A+B):=mul_le_mul_of_nonneg_right haH hsum
  have hdR':δ*A≤(p₀/4)*A:=mul_le_mul_of_nonneg_right hdR hA
  have hdH':δ*A≤(p₀*κ/2)*A:=mul_le_mul_of_nonneg_right hdH hA
  have hr:p₀/2≤pR*density:=by nlinarith [mul_nonneg (sub_nonneg.mpr hpR) (sub_nonneg.mpr hd)]
  have hr':(p₀/2)*A≤(pR*density)*A:=mul_le_mul_of_nonneg_right hr hA
  have hh:p₀*κ*A≤pH*B:=by
    have h1:=mul_le_mul_of_nonneg_left hBA hp₀.le
    have h2:=mul_le_mul_of_nonneg_right hpH hB
    nlinarith only [h1,h2]
  constructor
  · nlinarith [mul_nonneg hp₀.le (sub_nonneg.mpr hBA')]
  · nlinarith [mul_nonneg (mul_nonneg hp₀.le hκ.le) (sub_nonneg.mpr hBA')]
end Oberwolfach
