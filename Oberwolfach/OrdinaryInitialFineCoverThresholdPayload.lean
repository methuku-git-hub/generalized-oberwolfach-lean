module

public import Oberwolfach.OrdinaryInitialFineCoverFromSharedNamed

@[expose] public section
/-! Join the initial fine-cover threshold to the same beta-dependent payload
used for the matching, later geometry and protected vortex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_initial_fine_cover_threshold_payload
    (mWheel loadK d:ℕ)
    (ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar βcap δInitial δDeep δedit:ℝ)
    (hcover:∀β:ℝ,0≤β→β≤1/4→∃v₀:ℕ,1≤v₀ ∧
      OrdinaryInitialFineCoverFromSharedAt mWheel loadK d ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar β v₀)
    (Payload:ℝ→ℕ→ℕ→Prop)
    (hPayload:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,Payload β m₀ Nmin):
    ∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,∃mCert mInitial:ℕ,mCert≤m₀ ∧ mInitial≤m₀ ∧ Payload β mCert Nmin ∧
        OrdinaryInitialFineCoverFromSharedAt mWheel loadK d ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar β mInitial :=by
  intro β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mCert,Nmin,hcert⟩:=hPayload β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mInitial,_,hinitial⟩:=hcover β hβ.le hβ1
  exact ⟨max mCert mInitial,Nmin,mCert,mInitial,le_max_left _ _,le_max_right _ _,hcert,hinitial⟩
end Oberwolfach
