module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryAssignedEligibleFiberNormalization
public import Oberwolfach.OrdinaryAssignedEligibleFiberNormalization
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedActiveFiberNormalizationDirectReserve
public import Oberwolfach.OrdinaryAssignedActiveFiberNormalization
public import Oberwolfach.OrdinaryEligibleHost

@[expose] public section
/-! The assigned target masses normalize on the eligible host using the
same physical sample, with the auxiliary length fixed to m+1. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) eligibleFiberFin_candidate_direct_reserve (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_eligible_fiber_normalization_candidate_direct_reserve
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ ρ D:ℝ) (d m:ℕ) (hd:2≤d) (hm:7≤m)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (raw:RawMarkedOutcome (Fin n) U Bool Bool):
    let c:ℝ:=(m:ℝ)+1
    let a:=ordinaryAssignedLongWeight F hF K θ c
    let b:=ordinaryAssignedShortWeight F hF K i₀ rsv θ c
    let η:=fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i
    let p:=(∑u,(a u+b u))/D
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let st:=typedMarkedResourceState (ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw) (rawMarkedPairSpokes π d raw true true);
    ∀x:PhysicalSampledActive φ st,
      ∑z∈Finset.univ.filter (fun z=>φ z=x.val ∧ st z=true),
        ∑i:Option (Fin K),ordinaryMixedIdealTarget (m:ℝ) D p a b η i z=1 :=by
  intro c a b η p φ st
  have hc:8≤c:=by dsimp [c];exact_mod_cast (show 8≤m+1 by omega)
  have hnorm:=ordinary_assigned_active_fiber_normalization_candidate_direct_reserve hn F hF K hK i₀ rsv θ c ρ D d hd hs0 hs1 hθ hθ1 hc
    hda hρ hρ1 hD hsize Allowed hAllowed hClassReserve P π raw
  dsimp only at hnorm
  rw [ordinary_eligible_host_state P π d true true raw] at hnorm
  have hcm:c-1=(m:ℝ):=by dsimp [c];ring
  rw [hcm] at hnorm
  exact hnorm
end Oberwolfach
