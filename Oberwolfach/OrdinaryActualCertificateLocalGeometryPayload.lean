module

public import Oberwolfach.OrdinaryDeepLocalThresholdsWithExtra
public import Oberwolfach.OrdinaryVortexUniformGeometryCostThresholdPayload

@[expose] public section
/-! Extract both the local certificate thresholds and the uniform geometry
from the same chosen-load callback, using the same beta and row margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach

theorem ordinary_actual_certificate_local_geometry_payload
    (mWheel loadK d k:ℕ)
    (ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
      ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate δedit ηedit βcap δcap:ℝ)
    (lam ξreserve γgeom edit p βe βh εR εH βparent b B εparent gap βout ζout ηpack εout:ℝ)
    (hεR:0≤εR) (hεRcap:εR≤δcap) (hεH:0≤εH) (hεHcap:εH≤δcap)
    (Nextra:ℕ)
    (hsource:∀β:ℝ,0≤β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∀C:ℝ,0≤C→
      ∃mInitial mBalance mCover mEdit Nedit:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧ 1≤mEdit ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε ηbal cInitial δedit ηedit β d mEdit Nedit ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover ∧
      ∀εR' εH' pH:ℝ,0≤εR'→εR'≤δcap→0≤εH'→εH'≤δcap→0≤pH→pH≤1→
        OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh pH εR' εH'
          βparent b B εparent gap βout ζout ηpack εout):
    (∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,Nextra≤Nmin ∧ OrdinaryDeepLocalCertificateThresholdPayload mWheel loadK d
        ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
        ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate 0 δedit ηedit β m₀ Nmin) ∧
    (∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh 1 εR εH
        βparent b B εparent gap βout ζout ηpack εout) :=by
  have hthreshold:∀β:ℝ,0≤β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃mInitial mBalance mCover mEdit Nedit:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧ 1≤mEdit ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε ηbal cInitial δedit ηedit β d mEdit Nedit ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β 0 mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover:=by
    intro β hβ hβ1 hβcap hβInitial hβDeep hβedit
    obtain ⟨mI,mB,mC,mE,NE,hI,hB,hC,hE,hMatch,hInitial,hBalance,hCover,_⟩:=
      hsource β hβ hβ1 hβcap hβInitial hβDeep hβedit 0 (by norm_num)
    exact ⟨mI,mB,mC,mE,NE,hI,hB,hC,hE,hMatch,hInitial,hBalance,hCover⟩
  refine ⟨ordinary_deep_local_certificate_thresholds_with_extra mWheel loadK d
    ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
    ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate 0 δedit ηedit βcap Nextra hthreshold,?_⟩
  intro β hβ hβ1 hβcap hβInitial hβDeep hβedit
  obtain ⟨mI,mB,mC,mE,NE,hI,hB,hC,hE,hMatch,hInitial,hBalance,hCover,hgeometry⟩:=
    hsource β hβ.le hβ1 hβcap hβInitial hβDeep hβedit 0 (by norm_num)
  exact hgeometry εR εH 1 hεR hεRcap hεH hεHcap (by norm_num) (by norm_num)
end Oberwolfach
