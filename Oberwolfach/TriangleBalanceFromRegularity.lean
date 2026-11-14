module

public import Mathlib.Tactic

@[expose] public section
/-! Quantitative triangle row balance from approximate regularity, the
original rim/spoke density identity, and a small removed hub set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem triangle_balance_from_regularity
    (n U B D deg pR pH ε a ω p η:ℝ)
    (hn:0<n) (hω:0<ω) (hp:0<p) (hη:0≤η) (hε:0≤ε) (ha:0≤a)
    (hpR0:0≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hB:ω*n≤B) (hBU:B≤U) (hmiss:U-B≤a*n)
    (hnear:|deg-D|≤ε*n) (hidentity:pR*D=2*U*pH)
    (hscale:ε+2*a≤2*ω*p*η):
    |pR*deg/(2*B*pH)-1|≤η:=by
  have hpH0:0<pH:=hp.trans_le hpH
  have hB0:0<B:=(mul_pos hω hn).trans_le hB
  have hy:0<2*B*pH:=by positivity
  have hmiss0:0≤U-B:=by linarith
  have he:|pR*(deg-D)|≤ε*n:=by
    rw [abs_mul,abs_of_nonneg hpR0]
    calc
      _≤pR*(ε*n):=mul_le_mul_of_nonneg_left hnear hpR0
      _≤1*(ε*n):=mul_le_mul_of_nonneg_right hpR1 (by positivity)
      _=_:=by ring
  have hm:pH*(U-B)≤a*n:=by
    have hh:=mul_le_mul_of_nonneg_right hpH1 hmiss0
    nlinarith only [hh,hmiss]
  have hpHm:0≤pH*(U-B):=mul_nonneg hpH0.le hmiss0
  have hnumlo:-(ε+2*a)*n≤pR*deg-2*B*pH:=by
    nlinarith [(abs_le.mp he).1]
  have hnumhi:pR*deg-2*B*pH≤(ε+2*a)*n:=by
    nlinarith [(abs_le.mp he).2]
  have hden:2*ω*n*p≤2*B*pH:=by
    have hh:=mul_le_mul hB hpH (le_of_lt hp) hB0.le
    nlinarith only [hh]
  have hs:=mul_le_mul_of_nonneg_right hscale hn.le
  have hd:=mul_le_mul_of_nonneg_left hden hη
  have hlow:-η*(2*B*pH)≤pR*deg-2*B*pH:=by nlinarith [hnumlo]
  have hhigh:pR*deg-2*B*pH≤η*(2*B*pH):=by nlinarith [hnumhi]
  have heq:pR*deg/(2*B*pH)-1=(pR*deg-2*B*pH)/(2*B*pH):=by field_simp
  rw [heq]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hy).mpr
    nlinarith [hlow]
  · apply (div_le_iff₀ hy).mpr
    nlinarith [hhigh]
end Oberwolfach
