module

public import Oberwolfach.LongAssignedAdaptiveWeightedLocalFamilyLateScale
public import Oberwolfach.SuppliedVortexEventInnerColumnLocalFamily
public import Oberwolfach.LongAssignedAdaptiveWeightedInnerColumnRimRow
public import Oberwolfach.SuppliedVortexEventInnerColumnRimRow
public import Oberwolfach.LongAssignedAdaptiveWeightedInnerColumn
public import Oberwolfach.SuppliedVortexEventInnerColumn
public import Oberwolfach.SuppliedVortexFixedSpacingEventWithStarts

@[expose] public section
/-! The full supplied-vortex continuation can be invoked at fixed spacing;
the matching tolerance is chosen later and remains positive. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_fixed_spacing_event_choices_with_inner_column_and_local_rim_family
    (r k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (hγcap:γRich≤αRef)
    (htstar:0<tstar) (htstar1:tstar≤1) (horder:tstar≤sstar) (hkstar:0<kstar)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ ρ₀:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hωBound:4*ω≤ρ₀)
    (ζret:ℝ) (hζret:0<ζret)
    (ε₀ lam:ℝ) (hε₀:ε₀<1) (hlam:0<lam) (hlamθ:lam≤θ)
    (d:ℕ) (hd:2≤d) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ) (hspace:1/(8*(d:ℝ))≤θ/2):
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
      let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
      let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
      0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
      ∀(BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i),
        SuppliedVortexFixedSpacingEventWithInnerColumnAndLocalRimFamily r k₀ Qpow hr hQpow hlen αRef sstar ω γRich tstar kstar
          hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap htstar htstar1 horder hkstar
          K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret hζret ε₀ lam hε₀ hlam hlamθ eps d hd hcut BM hBM BO hBO:=by
  obtain ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,hOuter⟩:=
    long_assigned_adaptive_fixed_spacing_weighted_with_late_local_rim_family r k₀ Qpow hr hQpow hlen
      αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap
      htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret hζret ε₀ lam hε₀ hlam hlamθ d hd hcut hspace
  refine ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,?_⟩
  intro BM hBM BO hBO
  unfold SuppliedVortexFixedSpacingEventWithInnerColumnAndLocalRimFamily
  exact hOuter BM hBM BO hBO
end Oberwolfach
