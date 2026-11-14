module

public import Oberwolfach.OrdinaryDeepLocalThresholdMonotone

@[expose] public section
/-! Add every fixed local certificate and parent-size requirement before
choosing the common vortex size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_local_certificate_thresholds_with_extra
    (mWheel loadK d:ℕ)
    (ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
      ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate C δedit ηedit βcap:ℝ)
    (Nextra:ℕ)
    (hthreshold:∀β:ℝ,0≤β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃mInitial mBalance mCover mEdit Nedit:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧ 1≤mEdit ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε ηbal cInitial δedit ηedit β d mEdit Nedit ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover):
    ∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,Nextra≤Nmin ∧ OrdinaryDeepLocalCertificateThresholdPayload mWheel loadK d
        ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
        ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate C δedit ηedit β m₀ Nmin :=by
  intro β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨m₀,Nmin,hlocal⟩:=ordinary_deep_local_certificate_threshold_payload mWheel loadK d
    ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
    ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate C δedit ηedit βcap hthreshold
    β hβ hβ1 hβcap hInitial hDeep hEdit
  refine ⟨m₀,max Nmin Nextra,le_max_right _ _,?_⟩
  exact ordinary_deep_local_certificate_threshold_payload_mono mWheel loadK d
    ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
    ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate C δedit ηedit β
    m₀ Nmin m₀ (max Nmin Nextra) le_rfl (le_max_left _ _) hlocal
end Oberwolfach
