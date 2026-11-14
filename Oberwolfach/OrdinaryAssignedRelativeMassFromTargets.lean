module

public import Oberwolfach.OrdinaryAssignedRetainedMassRelative
public import Oberwolfach.OrdinaryAssignedRetainedMassDeviation
public import Oberwolfach.RetainedMassRelativeBudget
public import Oberwolfach.RetainedCommonHubCardUpper
public import Oberwolfach.OrdinaryMixedHubRootTarget
public import Oberwolfach.PhysicalSampledMixedHubDeviation
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! The actual retained hub-test mass has the factor-frequency target,
with the root and hub-count errors kept explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_retained_mass_relative_from_targets
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
    (b:U→ℝ) (hbdef:∀u,b u=ordinaryAssignedShortWeight F hF K i₀ rsv θ c u)
    (pstar lam:ℝ) (hpstar:0<pstar) (hbstar:∀u,pstar≤b u) (hlam:0≤lam)
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (a:U→ℝ) (D p:ℝ) (τ t countErr:ℝ) (hτ0:0≤τ) (ht0:0≤t) (hcount0:0≤countErr)
    (hτ:τ≤lam*pstar/4) (ht:t≤lam*(θ/(100*(K:ℝ)))/4)
    (hcountRate:countErr≤lam*pstar*n/4):
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
    (∀u,|((restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card:ℝ)-b u*n|≤countErr)→
    ∀z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ,
      let i:=z.val.1
      let u:=z.val.2
      let η:=ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i
      let count:ℝ:=(restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card
      let mass:=∑x:PhysicalSampledCandidate (mixedCandidateResources R) state,
        ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val*
          mixedCandidateWeight w x.val;
      |((longPaddedSeedExponent i+2:ℕ):ℝ)*mass-(1-θ)*ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i*n|≤
        lam*ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i*n :=by
  intro R w hub e hload hcount
  apply ordinary_assigned_retained_mass_relative hn F hF Allowed hAllowed hK i₀ rsv θ c
    hs0 hs1 hθ hθ1 hc hsclass hclass b hbdef pstar lam hpstar hbstar hlam π d m wM wO state
    τ t countErr hτ0 ht0 hcount0 hτ ht hcountRate
  · intro i u v hv hs
    have hh:=hload (some i) v hs
    rw [ordinary_mixed_hub_root_target (m:ℝ) D p a b
      (fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i) i u v hv] at hh
    exact hh
  · exact hcount
end Oberwolfach
