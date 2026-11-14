module

public import Oberwolfach.OrdinaryDeepLocalCertificateThresholdPayload

@[expose] public section
/-! Additional finite requirements can be folded into the terminal size
without changing the selected certificate thresholds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_local_certificate_threshold_payload_mono
    (mWheel loadK d:ℕ)
    (ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
      ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate C δedit ηedit β:ℝ)
    (m₀ Nmin m₁ N₁:ℕ) (hm:m₀≤m₁) (hN:Nmin≤N₁)
    (h:OrdinaryDeepLocalCertificateThresholdPayload mWheel loadK d
      ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
      ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate C δedit ηedit β m₀ Nmin):
    OrdinaryDeepLocalCertificateThresholdPayload mWheel loadK d
      ρ₀ α pmin hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ
      ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate C δedit ηedit β m₁ N₁ :=by
  obtain ⟨mInitial,mBalance,mCover,mEdit,Nedit,hi,hb,hc,he,hmi,hmb,hmc,hme,hNedit,hmatch,hinitial,hbalance,hcover⟩:=h
  exact ⟨mInitial,mBalance,mCover,mEdit,Nedit,hi,hb,hc,he,hmi.trans hm,hmb.trans hm,hmc.trans hm,hme.trans hm,
    hNedit.trans hN,hmatch,hinitial,hbalance,hcover⟩
end Oberwolfach
