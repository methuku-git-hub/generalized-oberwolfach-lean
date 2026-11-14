module

public import Oberwolfach.OrdinaryThreeStepBalanceProductAt

@[expose] public section
/-! Join the arbitrary-lookback balance threshold to the common terminal
size without changing the beta-dependent certificate payload. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_three_step_balance_threshold_payload
    (d:ℕ) (hd:2≤d) (εR εH ε ρ₀ χ βcap δInitial δDeep δedit:ℝ)
    (hεR:0<εR) (hεH:0<εH) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hχ:0<χ)
    (Payload:ℝ→ℕ→ℕ→Prop)
    (hPayload:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,Payload β m₀ Nmin):
    ∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,∃mCert mBalance:ℕ,mCert≤m₀ ∧ mBalance≤m₀ ∧ Payload β mCert Nmin ∧
        OrdinaryThreeStepBalanceProductAt d hd εR εH β ε ρ₀ χ mBalance :=by
  intro β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mCert,Nmin,hcert⟩:=hPayload β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mBalance,_,hbalance⟩:=ordinary_expanded_attach_three_step_balance_product_prior d hd εR εH β ε ρ₀ χ
    hεR hεH hβ.le hβ1 hε hε1 hρ₀ hχ
  exact ⟨max mCert mBalance,Nmin,mCert,mBalance,le_max_left _ _,le_max_right _ _,hcert,hbalance⟩
end Oberwolfach
