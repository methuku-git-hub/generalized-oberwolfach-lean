module

public import Oberwolfach.OrdinaryBoundarySelectionMargins

@[expose] public section
/-! Separate support loss from the larger outside-class loss caused by the
    root cover, while keeping the same fresh factor budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_selection_margins
    (p εsup τ ν η ell κ ζ n:ℝ)
    (hp:0<p) (hp1:p≤1) (hκ:0<κ) (hζ:0<ζ) (hn:0≤n)
    (hε:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4)
    (hclass:τ+ν+ell≤ζ*κ*p/4) (hblock:ν+η≤ζ*κ*p/4)
    (hpκ:p≤4*ζ*κ) (hsqrt:20*Real.sqrt (2*p)≤ζ*κ/2)
    (horder:2≤ζ*κ*p*n/4):
    (p+εsup)*n+(τ*n+ν*n)≤(2*p)*n ∧
    (p^2+εsup)*n+2*(τ*n+ν*n)≤(2*p)^2*n ∧
    ∀a:ℝ,κ*n≤a→
      τ*n+ν*n+ell*n≤ζ*(p*a) ∧
      2*((2*p)*Real.sqrt (2*p)*n)+
        2*(Nat.ceil (4*((2*p)*Real.sqrt (2*p)*n)):ℝ)+(ν*n+η*n)≤ζ*(p*a) :=by
  have hsupport':τ*n+ν*n≤(p^2/4)*n:=by
    have hh:=mul_le_mul_of_nonneg_right hsupport hn
    nlinarith only [hh]
  have hblock':ν*n+η*n≤ζ*κ*p*n/4:=by
    have hh:=mul_le_mul_of_nonneg_right hblock hn
    nlinarith only [hh]
  have hclass':τ*n+ν*n+ell*n≤ζ*κ*p*n/4:=by
    have hh:=mul_le_mul_of_nonneg_right hclass hn
    nlinarith only [hh]
  obtain ⟨hdeg,hpair,hbudget⟩:=ordinary_boundary_selection_margins p εsup (τ*n+ν*n) (ν*n+η*n) κ ζ n
    hp hp1 hκ hζ hn hε hsupport' hpκ hsqrt hblock' horder
  refine ⟨hdeg,hpair,?_⟩
  intro a ha
  have ha':ζ*κ*p*n≤ζ*(p*a):=by
    have hh:=mul_le_mul_of_nonneg_left ha (mul_nonneg hζ.le hp.le)
    nlinarith only [hh]
  have hnonneg:0≤ζ*κ*p*n:=by positivity
  exact ⟨by nlinarith only [hclass',ha',hnonneg],(hbudget a ha).2⟩
end Oberwolfach
