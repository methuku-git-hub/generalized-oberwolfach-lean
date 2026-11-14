module

public import Oberwolfach.OrdinaryAssignedRetainedMassRelative
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedFrequencyCoefficient
public import Oberwolfach.CandidateOrdinaryAssignedRetainedMassDeviation
public import Oberwolfach.OrdinaryAssignedRetainedMassDeviation
public import Oberwolfach.RetainedMassRelativeBudget
public import Oberwolfach.RetainedCommonHubCardUpper
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

theorem ordinary_assigned_retained_mass_relative_candidate
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (F u) K)
    (b:U→ℝ) (hbdef:∀u,b u=ordinaryAssignedShortWeight F hF K i₀ rsv θ c u)
    (pstar lam:ℝ) (hpstar:0<pstar) (hbstar:∀u,pstar≤b u) (hlam:0≤lam)
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (τ t countErr:ℝ) (hτ0:0≤τ) (ht0:0≤t) (hcount0:0≤countErr)
    (hτ:τ≤lam*pstar/4) (ht:t≤lam*(θ/(100*(K:ℝ)))/4)
    (hcountRate:countErr≤lam*pstar*n/4):
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let w:=ordinaryMixedGenericWeight wM wO
    let hub:=ordinaryMixedGenericWheelHub (U:=U) (K:=K) π (3*d) m longPaddedSeedExponent
    let e:{v // v∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _;
    (∀i u v,v∈ordinaryCommonHubSpokeRoots u→state v=true→
      |resourcePatternLoad (R (some i)) (w (some i)) (fun _ _=>true) v state-
        ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i|≤
        t+τ*ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i)→
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
  intro R w hub e hload hcount z i u η count mass
  have hcoef:=ordinary_assigned_frequency_coefficient_candidate hn F hF Allowed hAllowed K hK i₀ rsv θ c
    hs0 hs1 hθ hθ1 hc hsclass hclass u
  have hη:0≤η:=(hcoef.2.1 i).1
  have hbalance:η*b u=(1-θ)*ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i:=by rw [hbdef u];exact hcoef.2.2 i
  have hcard:0≤count:=by dsimp [count];positivity
  have hcardmax:count≤n:=by
    have hh:=retained_common_hub_card_le state u
    have hh' : (restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card ≤ n := by
      convert hh using 1 <;> (try simp only [Fintype.card_fin]) <;> congr! 5
    have hcast := (show ((restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card:ℝ) ≤ (n:ℝ) by exact_mod_cast hh')
    convert hcast using 1 <;> (try simp only [count]) <;> congr! 5
  have hmin:0≤θ/(100*(K:ℝ)):=by
    have hK':0<(K:ℝ):=by exact_mod_cast hK
    positivity
  have hbudget:=retained_mass_relative_budget n count (b u) pstar η
    (ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i) (θ/(100*(K:ℝ))) θ lam t τ countErr
    (Nat.cast_nonneg n) hcard hcardmax hpstar (hbstar u) hη hmin z.property hθ.le (by linarith) hlam ht0 hτ0 hcount0
    hbalance ht hτ hcountRate
  have hh:=ordinary_assigned_retained_mass_deviation_candidate hn F hF Allowed hAllowed hK i₀ rsv θ c hs0 hs1 hθ hθ1 hc
    hsclass hclass b hbdef π d m wM wO state τ t countErr hload hcount z
  exact hh.trans hbudget
end Oberwolfach
