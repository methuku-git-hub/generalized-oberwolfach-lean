module

public import Oberwolfach.OrdinaryCleanupSeparatedMargins

@[expose] public section
/-! Quadratically small cover costs fit between the linear input boundary
margin and the smaller linear cleanup margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_separated_boundary_rate_margins
    (cBoundary cCover cRoot:ℝ) (hBoundary:0<cBoundary) (hCover:0≤cCover) (hRoot:0≤cRoot):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε:ℝ,0<ε→ε≤εcap→∀ηrate ellrate:ℝ,
      ηrate≤cRoot*ε^2→ellrate≤cCover*ε^2→
      cBoundary*ε/2+3*max ηrate ellrate≤cBoundary*ε ∧
      cBoundary*ε/2+2*ellrate≤cBoundary*ε :=by
  let M:ℝ:=max cCover cRoot+1
  have hM:0<M:=by dsimp [M];have hh:=le_max_left cCover cRoot;linarith
  let εcap:ℝ:=min 1 (cBoundary/(12*M))
  have hecap:0<εcap:=by dsimp [εcap];positivity
  refine ⟨εcap,hecap,min_le_left _ _,?_⟩
  intro ε hε he ηrate ellrate hη hell
  have heBound:ε≤cBoundary/(12*M):=he.trans (min_le_right _ _)
  have hcoeff:12*M*ε≤cBoundary:=by
    have hh:ε*(12*M)≤cBoundary:=(le_div_iff₀ (by positivity:0<12*M)).mp heBound
    nlinarith only [hh]
  have hsq:0≤ε^2:=sq_nonneg ε
  have hc1:cCover≤M:=by dsimp [M];have hh:=le_max_left cCover cRoot;linarith
  have hc2:cRoot≤M:=by dsimp [M];have hh:=le_max_right cCover cRoot;linarith
  have hmax:max ηrate ellrate≤M*ε^2:=by
    apply max_le
    · exact hη.trans (mul_le_mul_of_nonneg_right hc2 hsq)
    · exact hell.trans (mul_le_mul_of_nonneg_right hc1 hsq)
  have hcoeff':12*M*ε^2≤cBoundary*ε:=by
    have hh:=mul_le_mul_of_nonneg_right hcoeff hε.le
    nlinarith only [hh]
  have hnon:0≤M*ε^2:=mul_nonneg hM.le hsq
  constructor
  · nlinarith only [hmax,hcoeff',hnon]
  · have hh:=hell.trans (mul_le_mul_of_nonneg_right hc1 hsq)
    nlinarith only [hh,hcoeff',hnon]
end Oberwolfach
