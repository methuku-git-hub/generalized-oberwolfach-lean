module

public import Oberwolfach.OrdinaryVortexGeometryCostBalanceThresholdPayload
public import Oberwolfach.OrdinaryDeepLocalCertificateThresholdPayload
public import Oberwolfach.OrdinaryInitialFineCoverFromSharedNamed

@[expose] public section
/-! Unpack the one selected vortex payload into the exact finite thresholds
and local inputs shared by initial and later wheel certificates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_geometry_fine_payload_inputs
    (mWheel loadK d k m₀ Nmin Nextra mv:ℕ)
    (ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γ edit p βe βh εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout cap rate β:ℝ)
    (α pmin hmin href δcut ζcut εcut ζlimit εsample a ρ θ cBoundary cInitial
      δInitial ηProfile ζ δDeep δedit ηedit αcut pstar:ℝ)
    (hpayload:OrdinaryVortexGeometryCostPayload mWheel loadK d k ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γ edit p βe βh εR εH
      βparent b B εparent gap βout ζout ηpack εout cap rate β
      (fun β' m' N'=>∃mLocal mFine:ℕ,mLocal≤m' ∧ mFine≤m' ∧
        (Nextra≤N' ∧ OrdinaryDeepLocalCertificateThresholdPayload mWheel loadK d
          ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
          ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate 0 δedit ηedit β' mLocal N') ∧
        OrdinaryInitialFineCoverFromSharedAt mWheel loadK d ρ₀ hmin href a ρ θ δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar β' mFine)
      m₀ Nmin)
    (hmv:m₀≤mv):
    ∃mGeom mCost mFine mInitial mBalance mCover mEdit Nedit:ℕ,
      mGeom≤mv ∧ mCost≤mv ∧ mFine≤mv ∧ mInitial≤mv ∧ mBalance≤mv ∧ mCover≤mv ∧ mEdit≤mv ∧
      Nextra≤Nmin ∧ Nedit≤Nmin ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε ηbal cInitial δedit ηedit β d mEdit Nedit ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β 0 mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover ∧
      OrdinaryInitialFineCoverFromSharedAt mWheel loadK d ρ₀ hmin href a ρ θ δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar β mFine ∧
      (∀pH:ℝ,0≤pH→pH≤1→
        OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold mWheel loadK d k mGeom β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γ edit p βe βh pH εR εH
          βparent b B εparent gap βout ζout ηpack εout) ∧
      OrdinarySelectedCostAtSpacing ε ρ₀ cap d rate β mCost :=by
  obtain ⟨mGeoPayload,mCost,hGeoSize,hCostSize,⟨mCert,mGeom,hCertSize,hGeomSize,hLocal,hGeometry⟩,hCost⟩:=hpayload
  obtain ⟨mLocal,mFine,hLocalSize,hFineSize,⟨hExtra,hPayload⟩,hFine⟩:=hLocal
  obtain ⟨mInitial,mBalance,mCover,mEdit,Nedit,_,_,_,_,hInitialSize,hBalanceSize,hCoverSize,hEditSize,hEditN,hMargins,hInitial,hBalance,hCover⟩:=hPayload
  refine ⟨mGeom,mCost,mFine,mInitial,mBalance,mCover,mEdit,Nedit,?_,?_,?_,?_,?_,?_,?_,hExtra,hEditN,
    hMargins,hInitial,hBalance,hCover,hFine,hGeometry,hCost⟩ <;> omega
end Oberwolfach
