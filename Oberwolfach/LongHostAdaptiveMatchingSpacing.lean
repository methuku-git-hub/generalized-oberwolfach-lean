module

public import Oberwolfach.LongHostAdaptiveSharedChoices

@[expose] public section
/-! Align the supplied-event spacing with the host weights whose bounds are
chosen after that spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_host_adaptive_matching_spacing
    (r k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (hγcap:γRich≤αRef)
    (htstar:0<tstar) (htstar1:tstar≤1) (horder:tstar≤sstar) (hkstar:0<kstar)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ ρ₀:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hωBound:4*ω≤ρ₀)
    (ε₀ lam:ℝ) (hε₀:ε₀<1) (hlam:0<lam) (hlamθ:lam≤θ)
    (αHost A BM:ℝ) (hBM:0<BM)
    (hHost:∀d:ℕ,2≤d→∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ HostMatchingVortexContinuation (r+4) K d αHost A BM BO):
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
    ∃d:ℕ,∃hd:2≤d,∃hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ,
    let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))
    0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
    ∃BO:Fin K→ℝ,∃hBO:∀i,0<BO i,
    HostMatchingVortexContinuation (r+4) K d αHost A BM BO ∧
    SuppliedVortexEventContinuation r k₀ Qpow hr hQpow hlen
      αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 horder hkstar
      K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO := by
  obtain ⟨eps,heps,heps1,hepsAssign,d,hd,hcut,halpha,halphaMass,hγ,hγε,hq⟩:=
    long_assigned_adaptive_supplied_vortex_weighted_fixed_ordered r k₀ Qpow hr hQpow hlen
      αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 horder hkstar
      K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
  obtain ⟨BO,hBO,hhost⟩:=hHost d hd
  have hEvent:SuppliedVortexEventContinuation r k₀ Qpow hr hQpow hlen
      αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 horder hkstar
      K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO:=hq BM hBM BO hBO
  exact ⟨eps,heps,heps1,hepsAssign,d,hd,hcut,halpha,halphaMass,hγ,hγε,BO,hBO,hhost,hEvent⟩
end Oberwolfach
