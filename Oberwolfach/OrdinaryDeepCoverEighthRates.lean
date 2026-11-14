module

public import Oberwolfach.OrdinaryCleanupSeparatedMargins

@[expose] public section
/-! The third-level root set and quadratic cover load yield quadratic
normalized cover and correction rates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_cover_eighth_rates
    (m:ℕ) (cLoad:ℝ) (hLoad:0<cLoad):
    ∃cCover cRoot:ℝ,0<cCover ∧ 0<cRoot ∧
    ∀(ε n N I T W ξroot:ℝ),0<ε→ε≤1→0≤n→n≤N→0≤I→I≤n→0≤T→0≤W→0≤ξroot→
      T+W≤2*ε^9*n→ξroot≤(cLoad*ε^8)^2/160→
      let ell:=max (18*(cLoad*ε^8)*n+3*(W+T))
        (3*(cLoad*ε^8)*n*((m:ℝ)+1)+T*((m:ℝ)+1));
      ell≤cCover*ε^8*N ∧ 10*ξroot*I≤cRoot*ε^8*N :=by
  let R:ℝ:=(m:ℝ)+1
  have hR:0<R:=by dsimp [R];positivity
  let cCover:ℝ:=18*cLoad+6+(3*cLoad+2)*R
  let cRoot:ℝ:=cLoad^2/16
  have hcCover:0<cCover:=by dsimp [cCover];positivity
  have hcRoot:0<cRoot:=by dsimp [cRoot];positivity
  refine ⟨cCover,cRoot,hcCover,hcRoot,?_⟩
  intro ε n N I T W ξroot hε hε1 hn hnN hI hIn hT hW hξ hroots hξbound ell
  have hN:0≤N:=hn.trans hnN
  have hIN:I≤N:=hIn.trans hnN
  have hsq0:0≤ε^8:=pow_nonneg hε.le 8
  have hsq1:ε^8≤1:=pow_le_one₀ hε.le hε1
  have hcube:ε^9≤ε^8:=by
    have hh:=mul_le_mul_of_nonneg_left (sub_nonneg.mpr hε1) hsq0
    nlinarith only [hh]
  have hfour:ε^16≤ε^8:=by
    have hh:=mul_le_mul_of_nonneg_left (sub_nonneg.mpr hsq1) hsq0
    nlinarith only [hh]
  have hroots2:T+W≤2*ε^8*n:=by
    have hh:=mul_le_mul_of_nonneg_right hcube hn
    nlinarith only [hroots,hh]
  have hTN:T≤2*ε^8*N:=by
    have hh:=mul_le_mul_of_nonneg_left hnN (show 0≤2*ε^8 by positivity)
    nlinarith only [hroots2,hh,hW]
  have hsumN:T+W≤2*ε^8*N:=by
    have hh:=mul_le_mul_of_nonneg_left hnN (show 0≤2*ε^8 by positivity)
    nlinarith only [hroots2,hh]
  have hloadN:(cLoad*ε^8)*n≤(cLoad*ε^8)*N:=mul_le_mul_of_nonneg_left hnN (by positivity)
  have hfirst:18*(cLoad*ε^8)*n+3*(W+T)≤cCover*ε^8*N:=by
    dsimp [cCover]
    have hpositive:0≤(3*cLoad+2)*R*ε^8*N:=by positivity
    nlinarith only [hloadN,hsumN,hpositive]
  have hsecond:3*(cLoad*ε^8)*n*((m:ℝ)+1)+T*((m:ℝ)+1)≤cCover*ε^8*N:=by
    have hh:=mul_le_mul_of_nonneg_right hloadN (show 0≤3*R by positivity)
    have hh':=mul_le_mul_of_nonneg_right hTN hR.le
    dsimp [cCover,R] at *
    have hpositive:0≤(18*cLoad+6)*ε^8*N:=by positivity
    nlinarith only [hh,hh',hpositive]
  have hrootCoeff:10*ξroot≤cRoot*ε^8:=by
    have hh:=mul_le_mul_of_nonneg_left hfour (show 0≤cLoad^2/16 by positivity)
    dsimp [cRoot]
    nlinarith only [hξbound,hh]
  have hroot:10*ξroot*I≤cRoot*ε^8*N:=by
    have hh:=mul_le_mul_of_nonneg_right hrootCoeff hI
    have hh':=mul_le_mul_of_nonneg_left hIN (show 0≤cRoot*ε^8 by positivity)
    nlinarith only [hh,hh']
  exact ⟨max_le hfirst hsecond,hroot⟩
end Oberwolfach
