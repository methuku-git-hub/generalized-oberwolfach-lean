module

public import Oberwolfach.SuppliedVortexEventBalancedDegree
public import Oberwolfach.LongAssignedAdaptiveBalancedDegreeWeightedFirstVortex
public import Oberwolfach.SuppliedVortexEventFirstInnerColumnOrderedLocalRetention
public import Oberwolfach.LongAssignedAdaptiveWeightedFirstVortexMargins

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem long_fixed_spacing_event_with_balanced_degree_tests
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
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i):
    SuppliedVortexFixedSpacingEventWithBalancedDegreeTests r k₀ Qpow hr hQpow hlen
      αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap
      htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret hζret d hd hcut BM hBM BO hBO:=by
  unfold SuppliedVortexFixedSpacingEventWithBalancedDegreeTests
  exact long_assigned_adaptive_balanced_degree_fixed_spacing_weighted_first_vortex_margins_with_local_retention r k₀ Qpow hr hQpow hlen
    αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap
    htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret hζret d hd hcut hspace BM hBM BO hBO
end Oberwolfach
