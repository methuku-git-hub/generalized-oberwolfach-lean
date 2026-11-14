module

public import Oberwolfach.BoundaryReserveSupportAfterPacking

@[expose] public section
/-! A concrete small-density hierarchy discharges the overlap, change and
integer-rounded factor-selection margins at a linear-size boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_boundary_selection_margins
    (p ε L δ κ ζ n:ℝ) (hp:0<p) (hp1:p≤1) (hκ:0<κ) (hζ:0<ζ) (hn:0≤n)
    (hε:ε≤p^2/4) (hL:L≤(p^2/4)*n) (hpκ:p≤4*ζ*κ)
    (hsqrt:20*Real.sqrt (2*p)≤ζ*κ/2)
    (hδ:δ≤ζ*κ*p*n/4) (horder:2≤ζ*κ*p*n/4):
    (p+ε)*n+L≤(2*p)*n ∧
    (p^2+ε)*n+2*L≤(2*p)^2*n ∧
    ∀a:ℝ,κ*n≤a→
      L≤ζ*(p*a) ∧
      2*((2*p)*Real.sqrt (2*p)*n)+
        2*(Nat.ceil (4*((2*p)*Real.sqrt (2*p)*n)):ℝ)+δ≤ζ*(p*a):=by
  have hp2:p^2≤p:=by nlinarith only [hp.le,hp1,mul_nonneg hp.le (sub_nonneg.mpr hp1)]
  have heN:=mul_le_mul_of_nonneg_right hε hn
  have hpN:=mul_le_mul_of_nonneg_right hp2 hn
  have hscale:p^2/4≤ζ*κ*p:=by nlinarith only [mul_le_mul_of_nonneg_right hpκ hp.le]
  have hscaleN:=mul_le_mul_of_nonneg_right hscale hn
  have hsN:=mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hp.le hn)
  have hceil:(Nat.ceil (4*((2*p)*Real.sqrt (2*p)*n)):ℝ)≤
      4*((2*p)*Real.sqrt (2*p)*n)+1:=
    (Nat.ceil_lt_add_one (by positivity:(0:ℝ)≤4*((2*p)*Real.sqrt (2*p)*n))).le
  refine ⟨?_,?_,?_⟩
  · nlinarith only [heN,hpN,hL,mul_nonneg hp.le hn]
  · nlinarith only [heN,hL,mul_nonneg (sq_nonneg p) hn]
  · intro a ha
    have ha' := mul_le_mul_of_nonneg_left ha (mul_nonneg hζ.le hp.le)
    constructor
    · nlinarith only [hL,hscaleN,ha']
    · nlinarith only [hceil,hsN,hδ,horder,ha']
end Oberwolfach
