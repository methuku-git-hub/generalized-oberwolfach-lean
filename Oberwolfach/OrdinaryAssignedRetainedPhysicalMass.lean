module

public import Oberwolfach.OrdinaryAssignedRetainedHubTests
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

theorem ordinary_assigned_retained_physical_mass
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK3:3≤K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
    (b:U→ℝ) (hbdef:∀u,b u=ordinaryAssignedShortWeight F hF K i₀ rsv θ c u)
    (hb:∀u,0<b u ∧ b u≤1) (pstar:ℝ) (hpstar:0<pstar) (hbstar:∀u,pstar≤b u)
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (τ t countErr:ℝ) (hτ:τ≤1/2) (ht:t≤θ/(800*(K:ℝ))) (hcountErr:countErr≤pstar*n/2):
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
      θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ))≤
        ∑c:PhysicalSampledCandidate (mixedCandidateResources R) state,
          ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z c.val*
            mixedCandidateWeight w c.val :=by
  intro R w hub e hload hcount z
  let i:=z.val.1
  let u:=z.val.2
  let η:=ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i
  let freq:=ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i
  have hK:0<K:=by omega
  have hKr:0<(K:ℝ):=by exact_mod_cast hK
  have hθhalf:θ≤1/2:=by linarith
  have hcoef:=ordinary_assigned_frequency_coefficient hn F hF Allowed hAllowed K hK i₀ rsv θ c
    hs0 hs1 hθ hθ1 hc hsclass hclass u
  have hη:0≤η:=(hcoef.2.1 i).1
  have hbalance:η*b u=(1-θ)*freq:=by rw [hbdef u];exact hcoef.2.2 i
  have hηlo:θ/(200*(K:ℝ))≤η:=ordinary_assigned_retained_coefficient_lower hn F hF Allowed hAllowed K hK i₀ rsv θ c
    hs0 hs1 hθ hθ1 hc hsclass hclass (fun u=>by rw [←hbdef u];exact (hb u).2) u i z.property
  have herr:t≤η/4:=by
    have heq:θ/(800*(K:ℝ))=(θ/(200*(K:ℝ)))/4:=by ring
    rw [heq] at ht
    linarith
  have hcard:b u*n/2≤(restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card:=by
    have hh:=abs_le.mp (hcount u)
    have hbn:=mul_le_mul_of_nonneg_right (hbstar u) (Nat.cast_nonneg n)
    linarith [hh.1]
  have hr:0<longPaddedSeedExponent i+2:=by have hh:=long_padded_seed_exponent_positive i;omega
  have hrmax:((longPaddedSeedExponent i+2:ℕ):ℝ)≤K:=by
    rw [long_padded_seed_length_eq_exponent]
    exact_mod_cast long_assigned_padded_length_upper hK3 i
  let g:=mixedHubIndicator hub (some i) u
  have hz:∀j,j≠some i→∀c,g j c=0:=mixed_hub_indicator_other_family hub (some i) u
  have hg:∀c,g (some i) c=if hub (some i) c=u then 1 else 0:=mixed_hub_indicator_same_family hub (some i) u
  have hS:∀c,(R (some i) c∩ordinaryCommonHubSpokeRoots u).card=
      if hub (some i) c=u then longPaddedSeedExponent i+2 else 0:=by
    intro c
    exact ordinary_mixed_generic_hub_spoke_count π (3*d) m longPaddedSeedExponent i u c
  have hmass:=physical_sampled_hub_frequency_margin R state w (some i) g (hub (some i)) u
    (ordinaryCommonHubSpokeRoots u) (longPaddedSeedExponent i+2) hr hz hg hS
    n (b u) η freq (θ/(100*(K:ℝ))) θ τ t K (Nat.cast_nonneg n) (hb u).1 hη z.property
    (by positivity) hθhalf hτ herr hrmax hbalance (hload i u) hcard
  have heq:(θ/(100*(K:ℝ)))*(n:ℝ)/(16*(K:ℝ))=θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ)):=by ring
  rw [heq] at hmass
  convert hmass using 1 <;> (try simp only [ordinaryAssignedRetainedHubIndicator,g,hub,i,u]) <;> congr! 5
end Oberwolfach
