module

public import Oberwolfach.OrdinaryTriangleInnerBoundaryChoice

@[expose] public section
/-! The stricter matching allowance used for boundary cleanup implies the
factor's own inequalities whenever it is below the factor margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_matching_margin_promote
    (θ θfactor p n τ ν η ell:ℝ) (hθ:θ≤θfactor) (hp:0≤p) (hn:0≤n)
    (hclass:τ+ν+ell≤θ*p/4) (hblock:ν+η≤θ*p/4)
    (hpθ:p≤4*θ) (hsqrt:20*Real.sqrt (2*p)≤θ/2) (horder:2≤θ*p*n/4):
    τ+ν+ell≤θfactor*p/4 ∧ ν+η≤θfactor*p/4 ∧ p≤4*θfactor ∧
      20*Real.sqrt (2*p)≤θfactor/2 ∧ 2≤θfactor*p*n/4:=by
  have hp':θ*p/4≤θfactor*p/4:=by
    have hh:=mul_le_mul_of_nonneg_right hθ hp
    nlinarith only [hh]
  have hn':θ*p*n/4≤θfactor*p*n/4:=by
    have hh:=mul_le_mul_of_nonneg_right hp' hn
    nlinarith only [hh]
  exact ⟨hclass.trans hp',hblock.trans hp',by linarith only [hpθ,hθ],
    by linarith only [hsqrt,hθ],horder.trans hn'⟩
end Oberwolfach
