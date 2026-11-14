module

public import Oberwolfach.OrdinaryAsymmetricSampledCoverGeometryLateRate

@[expose] public section
/-! Convert the actual fine triangle cover and root-row budgets into the
normalized rates required by the cleanup and likely-cover certificate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_cover_normalized_rates
    (nV nU nI nT nW ξ κ lam ellCap finishCap:ℝ)
    (hnV:0<nV) (hnU:0≤nU) (hnI:0≤nI) (hIV:nI≤nV)
    (hnT:0≤nT) (hnW:0≤nW) (hroot:nT+nW≤lam*nV)
    (hξ:0≤ξ) (hκ:0≤κ) (hlam:0≤lam) (hellCap:0≤ellCap) (hfinish:0≤finishCap)
    (hell:max (18*κ+3*lam) ((3*κ+lam)*3)≤ellCap) (hcover:10*ξ≤finishCap):
    let cover:=10*ξ*nI;
    let ell:=max (18*κ*nV+3*(nW+nT)) (3*κ*nV*3+nT*3);
    ∃ηrate ellrate:ℝ,0≤ηrate ∧ ηrate≤finishCap ∧ 0≤ellrate ∧ ellrate≤ellCap ∧
      cover=ηrate*(nV+nU) ∧ ell=ellrate*(nV+nU) :=by
  intro cover ell
  have hn:0<nV+nU:=by linarith
  have hnV0:0≤nV:=hnV.le
  have hN:nV≤nV+nU:=by linarith
  have hcoef1:18*κ+3*lam≤ellCap:=(le_max_left _ _).trans hell
  have hcoef2:(3*κ+lam)*3≤ellCap:=(le_max_right _ _).trans hell
  have h1:18*κ*nV+3*(nW+nT)≤ellCap*(nV+nU):=by
    have hsmall:=mul_le_mul_of_nonneg_left hroot (show (0:ℝ)≤3 by norm_num)
    have hcoef:=mul_le_mul_of_nonneg_right hcoef1 hnV0
    have hsize:=mul_le_mul_of_nonneg_left hN hellCap
    nlinarith
  have h2:3*κ*nV*3+nT*3≤ellCap*(nV+nU):=by
    have hT:nT≤lam*nV:=by linarith
    have hsmall:=mul_le_mul_of_nonneg_left hT (show (0:ℝ)≤3 by norm_num)
    have hcoef:=mul_le_mul_of_nonneg_right hcoef2 hnV0
    have hsize:=mul_le_mul_of_nonneg_left hN hellCap
    nlinarith
  have hell0:0≤ell:=by dsimp [ell];positivity
  have hellN:ell≤ellCap*(nV+nU):=by dsimp [ell];exact max_le h1 h2
  have hcover0:0≤cover:=by dsimp [cover];positivity
  have hcoverN:cover≤finishCap*(nV+nU):=by
    dsimp [cover]
    have hsmall:=mul_le_mul_of_nonneg_left hIV (show 0≤10*ξ by positivity)
    have hcoef:=mul_le_mul_of_nonneg_right hcover hnV0
    have hsize:=mul_le_mul_of_nonneg_left hN hfinish
    nlinarith
  refine ⟨cover/(nV+nU),ell/(nV+nU),div_nonneg hcover0 hn.le,?_,div_nonneg hell0 hn.le,?_,?_,?_⟩
  · exact (div_le_iff₀ hn).2 hcoverN
  · exact (div_le_iff₀ hn).2 hellN
  · field_simp
  · field_simp
end Oberwolfach
