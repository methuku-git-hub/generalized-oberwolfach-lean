module

public import Oberwolfach.OrdinaryActualCertificateGeometryAt

@[expose] public section
/-! Collect the initial-edit, initial-balance, trace-balance and deep-cover
thresholds from one certificate into a single later vortex-size requirement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

def OrdinaryDeepLocalCertificateThresholdPayload
    (mWheel loadK d:ℕ)
    (ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
      ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate C δedit ηedit β:ℝ)
    (m₀ Nmin:ℕ):Prop :=
    ∃mInitial mBalance mCover mEdit Nedit:ℕ,
      1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧ 1≤mEdit ∧
      mInitial≤m₀ ∧ mBalance≤m₀ ∧ mCover≤m₀ ∧ mEdit≤m₀ ∧ Nedit≤Nmin ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε ηbal cInitial δedit ηedit β d mEdit Nedit ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover

theorem ordinary_deep_local_certificate_threshold_payload
    (mWheel loadK d:ℕ)
    (ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
      ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate C δedit ηedit βcap:ℝ)
    (hthreshold:∀β:ℝ,0≤β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃mInitial mBalance mCover mEdit Nedit:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧ 1≤mEdit ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε ηbal cInitial δedit ηedit β d mEdit Nedit ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover):
    ∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,OrdinaryDeepLocalCertificateThresholdPayload mWheel loadK d
        ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
        ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate C δedit ηedit β m₀ Nmin :=by
  intro β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mInitial,mBalance,mCover,mEdit,Nedit,hi,hb,hc,he,hmatch,hinitial,hbalance,hcover⟩:=
    hthreshold β hβ.le hβ1 hβcap hInitial hDeep hEdit
  refine ⟨max (max mInitial mBalance) (max mCover mEdit),Nedit,
    mInitial,mBalance,mCover,mEdit,Nedit,hi,hb,hc,he,?_,?_,?_,?_,le_rfl,hmatch,hinitial,hbalance,hcover⟩ <;> omega
end Oberwolfach
