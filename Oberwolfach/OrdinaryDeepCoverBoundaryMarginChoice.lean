module

public import Oberwolfach.OrdinaryDeepCoverQuadraticRates
public import Oberwolfach.OrdinarySeparatedBoundaryRateMargins

@[expose] public section
/-! The cover costs fit strictly inside the gap between the selected linear
input boundary tolerance and the smaller cleanup tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_cover_boundary_margin_choice
    (m:ℕ) (cLoad cBoundary:ℝ) (hLoad:0<cLoad) (hBoundary:0<cBoundary):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧
    ∀(ε n N I T W ξroot:ℝ),0<ε→ε≤εcap→0≤n→n≤N→0≤I→I≤n→0≤T→0≤W→0≤ξroot→
      T+W≤2*ε^3*n→ξroot≤(cLoad*ε^2)^2/160→
      let ell:=max (18*(cLoad*ε^2)*n+3*(W+T))
        (3*(cLoad*ε^2)*n*((m:ℝ)+1)+T*((m:ℝ)+1));
      (cBoundary*ε/2)*N+3*max (10*ξroot*I) ell≤(cBoundary*ε)*N ∧
      (cBoundary*ε/2)*N+2*ell≤(cBoundary*ε)*N :=by
  obtain ⟨cCover,cRoot,hcCover,hcRoot,hcover⟩:=ordinary_deep_cover_quadratic_rates m cLoad hLoad
  obtain ⟨εcap,hεcap,hεcap1,hmargin⟩:=ordinary_separated_boundary_rate_margins cBoundary cCover cRoot
    hBoundary hcCover.le hcRoot.le
  refine ⟨εcap,hεcap,hεcap1,?_⟩
  intro ε n N I T W ξroot hε he hn hnN hI hIn hT hW hξ hroots hξbound ell
  have he1:ε≤1:=he.trans hεcap1
  have hN:0≤N:=hn.trans hnN
  obtain ⟨hell,hroot⟩:=hcover ε n N I T W ξroot hε he1 hn hnN hI hIn hT hW hξ hroots hξbound
  have hmax:max (10*ξroot*I) ell≤max (cRoot*ε^2) (cCover*ε^2)*N:=by
    apply max_le
    · have hh:=mul_le_mul_of_nonneg_right (le_max_left (cRoot*ε^2) (cCover*ε^2)) hN
      exact hroot.trans hh
    · have hh:=mul_le_mul_of_nonneg_right (le_max_right (cRoot*ε^2) (cCover*ε^2)) hN
      exact hell.trans hh
  have hmarg:=hmargin ε hε he (cRoot*ε^2) (cCover*ε^2) le_rfl le_rfl
  have hfirst:=mul_le_mul_of_nonneg_right hmarg.1 hN
  have hsecond:=mul_le_mul_of_nonneg_right hmarg.2 hN
  constructor
  · nlinarith only [hfirst,hmax]
  · nlinarith only [hsecond,hell]
end Oberwolfach
