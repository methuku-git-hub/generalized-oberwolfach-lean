module

public import Oberwolfach.OrdinaryLookbackBalanceProductAt

@[expose] public section
/-! Combine the lookback-vortex and deeper-balance threshold with any
beta-dependent certificate thresholds before selecting the terminal size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_lookback_balance_threshold_payload
    (d:ℕ) (hd:2≤d) (εR εH ε ρ₀ χ βcap δInitial δDeep δedit:ℝ)
    (hεR:0<εR) (hεH:0<εH) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hχ:0<χ)
    (Payload:ℝ→ℕ→ℕ→Prop)
    (hPayload:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,Payload β m₀ Nmin):
    ∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,∃mCert mLook:ℕ,mCert≤m₀ ∧ mLook≤m₀ ∧ Payload β mCert Nmin ∧
        OrdinaryLookbackBalanceProductAt d hd εR εH β ε ρ₀ χ mLook :=by
  intro β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mCert,Nmin,hcert⟩:=hPayload β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mLook,_,hlook⟩:=ordinary_lookback_selected_balance_product_prior d hd εR εH β ε ρ₀ χ
    hεR hεH hβ hβ1 hε hε1 hρ₀ hχ
  exact ⟨max mCert mLook,Nmin,mCert,mLook,le_max_left _ _,le_max_right _ _,hcert,hlook⟩
end Oberwolfach
