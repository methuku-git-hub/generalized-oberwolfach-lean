module

public import Oberwolfach.OrdinaryActualResidualMassLower
public import Oberwolfach.OrdinaryMatchingResidualCycleMass
public import Oberwolfach.OrdinaryAssignedRetainedMass
public import Oberwolfach.ResidualLongMassArithmetic
public import Oberwolfach.ActualResidualSumIndices

@[expose] public section
/-! Derive the actual full-selection mass from the original start counts,
retention row bound, and the selected ordinary-cycle mass. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance ordinaryActualResidualMatchingFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_actual_residual_full_mass_from_matching
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100)
    (m d:ℕ) (hm:7≤m) (hd:1≤d) (θ:ℝ) (hθ:0<θ) (hθ1:θ≤1/100)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (ζ matchErr err:ℝ)
    (hgood:RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (w:U)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (hcounts:∀g:Bool,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/d|<(n:ℝ)^(3/4:ℝ)/d):
    let A:=retainedMarkedIndex π d σ false t Jret w
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) x true}
    ∀{S:Set (Fin n)} (a:ActualResidualData (K:=A⊕B)
      (J:=OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L w) ((F w).induce S))
    (hc:a.c=m+1) (hd':a.d=d) (hs₁:a.s₁=firstSumIndices) (hs₂:a.s₂=secondSumIndices)
    (ht:a.t=Finset.univ)
    (hEmbed:a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset))
    (hlen:∀j,(a.C j).length=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L w j).1+2)
    (hmatch:(1-θ-matchErr)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i)≤
      ((∑j:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L w,
        (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L w j).1+2)):ℝ))
    (herror:(n:ℝ)*(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g)/d+
       (((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+matchErr*n*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i)≤err*n),
    (1-rsv-2*θ-err)*n≤
      ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ)+
        ((a.c*a.d-1:ℕ):ℝ)*(a.s₁.card+a.s₂.card):=by
  intro A B S a hc hd' hs₁ hs₂ ht hEmbed hlen hmatch herror
  have hcycle:=ordinary_matching_residual_cycle_mass F hF i₀ rsv θ π d m RM state L w matchErr hmatch a ht hEmbed hlen
  exact ordinary_actual_residual_full_mass_lower hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 m d hm hd θ hθ hθ1 hrsclass hclass
    π σ t Jret ζ (matchErr*n*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i)) err hgood w hcounts
    a hc hd' hs₁ hs₂ hcycle herror
end Oberwolfach
