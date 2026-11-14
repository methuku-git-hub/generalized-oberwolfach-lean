module

public import Oberwolfach.OrdinaryAssignedPhysicalMassAfterDeletion
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedPhysicalMassFromTargets
public import Oberwolfach.OrdinaryAssignedPhysicalMassFromTargets
public import Oberwolfach.OrdinaryShiftedDeletedHubCard
public import Oberwolfach.OrdinaryMixedHubRootTarget
public import Oberwolfach.PhysicalSampledHubFrequencyMargin
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! Every retained ordinary factor-frequency test has positive mass among
the realized physical matching candidates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_retained_mass_after_rim_deletion_candidate
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK3:3≤K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (F u) K)
    (b:U→ℝ) (hbdef:∀u,b u=ordinaryAssignedShortWeight F hF K i₀ rsv θ c u)
    (hb:∀u,0<b u ∧ b u≤1) (pstar:ℝ) (hpstar:0<pstar) (hbstar:∀u,pstar≤b u)
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (P:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (Del:Finset (Sym2 (Fin n)))
    (a:U→ℝ) (D p:ℝ) (τ t countErr:ℝ) (hτ:τ≤1/2) (ht:t≤θ/(800*(K:ℝ))) (hcountErr:countErr≤pstar*n/2):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw Del
    let state:=typedMarkedResourceState (ordinaryShiftedPairRims P π d raw') (rawMarkedPairSpokes π d raw' true true)
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let w:=ordinaryMixedGenericWeight wM wO
    let hub:=ordinaryMixedGenericWheelHub (U:=U) (K:=K) π (3*d) m longPaddedSeedExponent
    let e:{v // v∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _;
    (∀i v,state v=true→
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v state-
        ordinaryMixedIdealTarget (m:ℝ) D p a b (fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i) i v|≤
        t+τ*ordinaryMixedIdealTarget (m:ℝ) D p a b (fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i) i v)→
    (∀u,|rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) true true false u Finset.univ-b u*n|≤countErr)→
    ∀z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ,
      θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ))≤
        ∑c:PhysicalSampledCandidate (mixedCandidateResources R) state,
          ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z c.val*
            mixedCandidateWeight w c.val :=by
  intro raw raw' state R w hub e hload hcount
  apply ordinary_assigned_retained_physical_mass_from_targets_candidate hn F hF Allowed hAllowed hK3 i₀ rsv θ c hs0 hs1 hθ hθ1 hc hsclass hclass
    b hbdef hb pstar hpstar hbstar π d m wM wO state a D p τ t countErr hτ ht hcountErr
  · exact hload
  · intro u
    have hh:=ordinary_shifted_deleted_hub_card P π d σ true true Del u
    have hc:((restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card:ℝ)=
        rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) true true false u Finset.univ:=by
      convert hh using 1 <;> congr! 5
    change |((restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card:ℝ)-b u*n|≤countErr
    rw [hc]
    exact hcount u
end Oberwolfach
