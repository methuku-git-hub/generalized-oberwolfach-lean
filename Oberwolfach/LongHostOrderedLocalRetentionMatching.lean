module

public import Oberwolfach.LongFixedSpacingOrderedLocalRetentionEvent
public import Oberwolfach.LongHostEventSpecializationOrderedLocalRetention
public import Oberwolfach.LongHostEventMatchingFirstInnerColumnOrderedLocalRetention

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem long_host_ordered_local_retention_and_matching
    (r k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (hγcap:γRich≤αRef)
    (htstar:0<tstar) (htstar1:tstar≤1) (horder:tstar≤sstar) (hkstar:0<kstar)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ ρ₀:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hωBound:4*ω≤ρ₀)
    (ζret:ℝ) (hζret:0<ζret) (d:ℕ) (hd:2≤d)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ) (hspace:1/(8*(d:ℝ))≤θ/2)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (αHost A:ℝ) (hαHost:0<αHost) (hαmargin:2*αRef≤αHost)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (hkBound:∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hHost:HostMatchingVortexContinuation (r+4) K d αHost A BM BO):
    HostVortexFixedSpacingEventConclusionWithFirstInnerColumnMatchingAndOrderedLocalRetentionRates r k₀ Qpow hr hQpow hlen
      αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap
      htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret hζret d hd hcut
      BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound:=by
  have hEvent:=long_fixed_spacing_event_first_vortex_matching_margins_with_local_retention r k₀ Qpow hr hQpow hlen
    αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap
    htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret hζret d hd hcut hspace BM hBM BO hBO
  have hOutcome:=long_host_fixed_spacing_event_specialization_first_vortex_matching_margins_with_local_retention r k₀ Qpow hr hQpow hlen
    αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap
    htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret hζret d hd hcut BM hBM BO hBO
    αHost A hαHost hαmargin htstarBound hkBound hHost hEvent
  exact host_vortex_fixed_spacing_event_with_first_inner_column_matching_and_ordered_local_retention_rates r k₀ Qpow hr hQpow hlen
    αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap
    htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret hζret d hd hcut BM hBM BO hBO
    αHost A hαHost hαmargin htstarBound hkBound hOutcome
end Oberwolfach
