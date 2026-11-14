module

public import Oberwolfach.LongRawOrdinaryDisjointPartialsProperty
public import Oberwolfach.LongPaddedPartialFactorsFromFrequencies
public import Oberwolfach.LongRawComponentMapsToPartialFactors
public import Oberwolfach.LongPaddedComponentMapsFromFrequenciesCompact
public import Oberwolfach.LongRawOrdinaryComponentMapsProperty
public import Oberwolfach.LongSelectedAssignmentFromFrequencies
public import Oberwolfach.LongRawAssignedComponentMapsFinal
public import Oberwolfach.LongSelectedAssignmentReindex
public import Oberwolfach.LongPaddedSelectedRetained
public import Oberwolfach.LongPaddedAssignmentFromAbsoluteFrequency

@[expose] public section
/-! Convert the existing selected-candidate component assignment to the
extracted ordinary-wheel indexing, preserving both hub and true length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longPaddedDisjointPartialsFrequencyDecidableFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_padded_ordinary_disjoint_partials_from_frequencies
    (hn:0<n) (hK:0<K) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m d:ℕ) (θ D:ℝ) (hθ:0<θ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (w:∀i,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (eps lam:ℝ)
    (hlam:0≤lam) (hlamθ:lam≤θ) (heps:eps≤lam*(θ/(100*(K:ℝ)^2))):
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let ℓ:=fun i=>ni i+2
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let wO:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let wmix:=longMixedSeedWeight wM wO
    let hub:=fun c:RestrictedResource (mixedCandidateResources R) e=>longRawSeedHub π d m ℓ c.val.1 c.val.2
    let idx:=fun c:RestrictedResource (mixedCandidateResources R) e=>c.val.1.getD ⟨0,hK⟩
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
      (∀c∈M,0<mixedCandidateWeight wmix c.val) →
      (∀c∈M,∀c'∈M,c≠c'→Disjoint
        (restrictedResourceSet (mixedCandidateResources R) e c)
        (restrictedResourceSet (mixedCandidateResources R) e c')) →
    (∀u i, θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u →
      let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((ni i+2:ℕ):ℝ)
      |(((M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card:ℝ)-(1-θ)*t)|≤eps*n) →
    LongRawOrdinaryDisjointPartialsProperty F P π d m ℓ raw g j M :=by
  intro ni hni ℓ state e R wO wmix hub idx M hpos hmatch herr
  have hp:=long_padded_ordinary_partial_factors_from_frequencies hn hK F hF m d θ D hθ P π w wM raw g j eps lam hlam hlamθ heps M hpos hmatch herr
  exact long_raw_partial_factors_pairwise_disjoint F P π d m ℓ raw g j M (by
    intro c hc c' hc' hne
    convert hmatch c hc c' hc' hne using 1 <;> congr 3 <;> exact Subsingleton.elim _ _) hp
end Oberwolfach
