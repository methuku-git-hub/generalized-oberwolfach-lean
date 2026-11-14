module

public import Oberwolfach.OrdinarySharpRootEditMargins
public import Oberwolfach.OrdinarySharpFineBalanceScaleChoiceCapped

@[expose] public section
/-! Convert the selected scalar rates into the three sharp balance margins
and the independent edit margin on a finite nonroot parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sharp_geometry_margin_arithmetic
    (m:ℕ) (n nfree inn t w q β εR εH conflict deepCost ξ κ η ηInitial γ edit lam:ℝ)
    (hn:0≤n) (hnfree:n/2≤nfree) (hi:0≤ inn) (hin:inn≤n)
    (ht:0≤t) (hw:0≤w) (htn:t≤n) (hwn:w≤n)
    (hq:0≤q) (hq1:q≤1) (hβ:0≤β) (hεR:0≤εR) (hεH:0≤εH)
    (hconf:0≤conflict) (hdeep:0≤deepCost) (hξ:0≤ξ) (hκ:0≤κ) (hη:0≤η) (hηI:0≤ηInitial)
    (hγ:0≤γ) (hedit:0<edit) (hlam:0≤lam)
    (hβcap:β≤γ/1000) (hRcap:εR≤γ/1000) (hHcap:εH≤γ/1000)
    (hconfCap:conflict≤(γ/1000)*n) (hξcap:ξ≤γ/160000) (hκcap:κ≤γ/1000)
    (hηcap:η≤γ/1000) (hηIcap:ηInitial≤η) (hdeepCap:deepCost≤10*ξ*n)
    (hroots:t+w≤lam*n) (hrow:3*lam≤edit/4) (hlevel:lam*((m:ℝ)+1)≤edit/4)
    (hκedit:κ≤edit/(72*((m:ℝ)+2))):
    let deep:=q*β*t+εR*t+2*(εH*w)+conflict+2*deepCost;
    let cover:=10*ξ*inn;let loss:=12*κ*n;let bin:=η*inn;let cin:=ηInitial*inn+2*deepCost;
    let ell:=max (18*κ*n+3*(w+t)) (3*κ*n*((m:ℝ)+1)+t*((m:ℝ)+1));
    0≤deep ∧ 0≤bin ∧ 0≤cin ∧
    deep+2*cover≤γ*nfree ∧ bin+deep+4*cover≤γ*nfree ∧ cin+deep+loss≤γ*nfree ∧
    ell≤edit*nfree:=by
  intro deep cover loss bin cin ell
  have hγn:0≤γ*n:=mul_nonneg hγ hn
  have hqβ:q*β≤β:=by nlinarith [mul_nonneg hβ (sub_nonneg.mpr hq1)]
  have hqβt:q*β*t≤β*n:=by
    calc
      q*β*t ≤ β*t:=mul_le_mul_of_nonneg_right hqβ ht
      _ ≤ β*n:=mul_le_mul_of_nonneg_left htn hβ
  have hβn:β*n≤(γ/1000)*n:=mul_le_mul_of_nonneg_right hβcap hn
  have hRn:εR*t≤(γ/1000)*n:=(mul_le_mul_of_nonneg_left htn hεR).trans (mul_le_mul_of_nonneg_right hRcap hn)
  have hHn:εH*w≤(γ/1000)*n:=(mul_le_mul_of_nonneg_left hwn hεH).trans (mul_le_mul_of_nonneg_right hHcap hn)
  have hξn:ξ*n≤(γ/160000)*n:=mul_le_mul_of_nonneg_right hξcap hn
  have hκn:κ*n≤(γ/1000)*n:=mul_le_mul_of_nonneg_right hκcap hn
  have hηn:η*inn≤(γ/1000)*n:=(mul_le_mul_of_nonneg_left hin hη).trans (mul_le_mul_of_nonneg_right hηcap hn)
  have hηIn:ηInitial*inn≤(γ/1000)*n:=(mul_le_mul_of_nonneg_right hηIcap hi).trans hηn
  have hξin:ξ*inn≤ξ*n:=mul_le_mul_of_nonneg_left hin hξ
  have hdeepBound:deep≤(γ/100)*n:=by
    dsimp [deep]
    nlinarith only [hqβt,hβn,hRn,hHn,hconfCap,hdeepCap,hξn,hγn]
  have hcoverBound:cover≤(γ/10000)*n:=by
    dsimp [cover]
    nlinarith only [hξin,hξn,hγn]
  have hlossBound:loss≤(γ/50)*n:=by
    dsimp [loss]
    nlinarith only [hκn,hγn]
  have hbinBound:bin≤(γ/1000)*n:=by simpa [bin] using hηn
  have hcinBound:cin≤(γ/500)*n:=by
    dsimp [cin]
    nlinarith only [hηIn,hdeepCap,hξn,hγn]
  have hfreeγ:(γ*n)/2≤γ*nfree:=by nlinarith [mul_le_mul_of_nonneg_left hnfree hγ]
  have hMargins:=ordinary_sharp_root_edit_margins m edit lam κ hedit hlam hκ hrow hlevel hκedit
  have hMn:0≤((m:ℝ)+1):=by positivity
  have htroot:t≤lam*n:=by linarith only [hroots,hw]
  have ha:18*κ*n+3*(w+t)≤(edit/2)*n:=by
    have hh:=mul_le_mul_of_nonneg_right hMargins.1 hn
    nlinarith only [hroots,hh]
  have hb:3*κ*n*((m:ℝ)+1)+t*((m:ℝ)+1)≤(edit/2)*n:=by
    have hh:=mul_le_mul_of_nonneg_right hMargins.2 hn
    have ht':=mul_le_mul_of_nonneg_right htroot hMn
    nlinarith only [hh,ht']
  have hfreeEdit:(edit/2)*n≤edit*nfree:=by nlinarith [mul_le_mul_of_nonneg_left hnfree hedit.le]
  refine ⟨by dsimp [deep];positivity,by dsimp [bin];positivity,by dsimp [cin];positivity,?_,?_,?_,?_⟩
  · nlinarith only [hdeepBound,hcoverBound,hfreeγ,hγn]
  · nlinarith only [hbinBound,hdeepBound,hcoverBound,hfreeγ,hγn]
  · nlinarith only [hcinBound,hdeepBound,hlossBound,hfreeγ,hγn]
  · dsimp [ell];exact max_le (ha.trans hfreeEdit) (hb.trans hfreeEdit)
end Oberwolfach
