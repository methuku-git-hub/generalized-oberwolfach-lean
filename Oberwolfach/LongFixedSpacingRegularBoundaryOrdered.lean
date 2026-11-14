module

public import Oberwolfach.SuppliedVortexRegularBoundaryOrderedEvent
public import Oberwolfach.LongAssignedAdaptiveBoundaryRegularWeightedOrdered
public import Oberwolfach.SuppliedVortexEventFirstInnerColumnOrderedLocalRetention
public import Oberwolfach.LongAssignedAdaptiveWeightedFirstVortexMargins

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem long_fixed_spacing_regular_boundary_ordered_event
    (r k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (hγcap:γRich≤αRef)
    (htstar:0<tstar) (htstar1:tstar≤1) (horder:tstar≤sstar) (hkstar:0<kstar)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ ρ₀:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hωBound:4*ω≤ρ₀)
    (ζret rPart:ℝ) (Bpart:ℕ) (hζret:0<ζret) (hrPart:0<rPart) (d:ℕ) (hd:2≤d)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ) (hspace:1/(8*(d:ℝ))≤θ/2)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i):
    SuppliedVortexFixedSpacingRegularBoundaryOrderedEvent r k₀ Qpow hr hQpow hlen
      αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap
      htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret rPart Bpart hζret hrPart d hd hcut BM hBM BO hBO:=by
  unfold SuppliedVortexFixedSpacingRegularBoundaryOrderedEvent
  exact long_assigned_adaptive_boundary_regular_weighted_ordered r k₀ Qpow hr hQpow hlen
    αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap
    htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret rPart Bpart hζret hrPart d hd hcut hspace BM hBM BO hBO
end Oberwolfach
