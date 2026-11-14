module

public import Oberwolfach.OrdinaryAssignedActiveFiberNormalization
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedApproximateDensityBounds
public import Oberwolfach.CandidateOrdinaryAssignedCoefficientBalance
public import Oberwolfach.OrdinaryShiftedActiveFiberNormalization
public import Oberwolfach.OrdinaryAssignedCoefficientBalance
public import Oberwolfach.OrdinaryAssignedApproximateDensityBounds

@[expose] public section
/-! The physical-fiber target identity for the actual assigned ordinary
marginals and the same categorical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryAssignedActiveFin_candidate (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_active_fiber_normalization_candidate
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,i₀∈factorShortCandidates (F w) K)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (raw:RawMarkedOutcome (Fin n) U Bool Bool):
    let a:=ordinaryAssignedLongWeight F hF K θ c
    let b:=ordinaryAssignedShortWeight F hF K i₀ rsv θ c
    let η:=fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i
    let p:=(∑u,(a u+b u))/D
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let good:=ordinaryPhysicalEligible (U:=U) π d
    let st:=typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw true true)
    let σ:=physicallyRestrictedState φ good st;
    ∀x:PhysicalSampledActive φ σ,
      ∑z∈Finset.univ.filter (fun z=>φ z=x.val ∧ σ z=true),
        ∑i:Option (Fin K),ordinaryMixedIdealTarget (c-1) D p a b η i z=1 :=by
  intro a b η p φ good st σ
  have hdens:=ordinary_assigned_approximate_density_bounds_candidate hn F hF K hK i₀ rsv θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
  have hp:0<p:=lt_of_lt_of_le hdens.1 hdens.2.1
  have hb:∀u,0<b u:=fun u=>lt_of_lt_of_le hdens.1 (hdens.2.2.2.1 u).1
  have hbalance:=ordinary_assigned_coefficient_balance_candidate hn F hF K hK i₀ rsv θ c
    hs0 hs1 hθ hθ1 hc Allowed hAllowed hsclass hclass
  have hbal:∀u,(c-1)*a u+(∑i,η i u)*b u=b u:=by
    intro u
    have hh:=hbalance u
    change (∑i,η i u)*b u+(c-1)*a u=b u at hh
    linarith
  have hpdef:(∑u,(a u+b u))=D*p:=by dsimp [p];field_simp
  have hnorm:=ordinary_shifted_active_fiber_normalization P π d true true raw (c-1) D p hD hp a b η hb hbal hpdef
  exact hnorm
end Oberwolfach
