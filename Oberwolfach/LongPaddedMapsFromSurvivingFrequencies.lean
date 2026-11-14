module

public import Oberwolfach.LongPaddedComplementFromSurviving
public import Oberwolfach.LongPaddedComponentMapsFromFrequenciesCompact

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longPaddedSurvivingMapsDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_padded_component_maps_from_surviving_frequencies
    (hn:0<n) (hK:0<K) (hK3:3≤K) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m d:ℕ) (θ D:ℝ) (hθ:0<θ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (hlong:∀u,(1/2:ℝ)≤
      ((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n)
    (w:∀i,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U)
    (Deleted:Finset (Sym2 (Fin n)))
    (eps lam:ℝ)
    (hlam:0≤lam) (hlamθ:lam≤θ) (heps:eps≤lam*(θ/(100*(K:ℝ)^2))):
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let ℓ:=fun i=>ni i+2
    let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false t J false false
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let state:=longRawHubState P π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let wO:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let wmix:=longMixedSeedWeight wM wO
    let T:=bernoulliVertexSet state
    let S:=longRawSurvivingResources P π d raw true true Deleted
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P π d raw true true Deleted)
    let es:{z // z∈S}↪_:=Function.Embedding.subtype _
    let hub:=fun c:RestrictedResource (mixedCandidateResources R) es=>longRawSeedHub π d m ℓ c.val.1 c.val.2
    MarkedFixedTerminalAbsorber P π d m selected H Reserve X Z →
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) es),
      (∀c∈M,0<mixedCandidateWeight wmix c.val) →
      (∀c∈M,∀c'∈M,c≠c'→Disjoint
        (restrictedResourceSet (mixedCandidateResources R) es c)
        (restrictedResourceSet (mixedCandidateResources R) es c')) →
    (∀u i, θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u →
      let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((ni i+2:ℕ):ℝ)
      |(((M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card:ℝ)-(1-θ)*t)|≤eps*n) →
    let N:=M.map q
    LongRawOrdinaryComponentMapsProperty F π d m ℓ e N :=by
  intro ni hni ℓ selected H raw state e R wO wmix T S q es hub habs M hpos hmatch herr N
  have hpos' : ∀c∈N,0<mixedCandidateWeight wmix c.val :=by
    intro c hc
    obtain ⟨b,hb,hbc⟩:=Finset.mem_map.mp hc
    subst c
    exact hpos b hb
  have hmatch' : ∀c∈N,∀c'∈N,c≠c'→Disjoint
      (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'):=by
    have hm := (long_raw_surviving_matching_lift P π d m ℓ raw true true Deleted M (by
      intro c hc c' hc' hne
      convert hmatch c hc c' hc' hne using 1 <;> congr 3 <;> exact Subsingleton.elim _ _)).1
    intro c hc c' hc' hne
    convert hm c hc c' hc' hne using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  have herr' : ∀u i, θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u →
      let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((ni i+2:ℕ):ℝ)
      |(((N.filter (fun c=>c.val.1=some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card:ℝ)-(1-θ)*t)|≤eps*n:=by
    intro u i hi
    have hc:((N.filter (fun c=>c.val.1=some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card)=
        ((M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card) :=by
      convert (long_raw_surviving_matching_lift P π d m ℓ raw true true Deleted M (by
        intro c hc c' hc' hne
        convert hmatch c hc c' hc' hne using 1 <;> congr 3 <;> exact Subsingleton.elim _ _)).2.1 (some i) u using 1 <;> congr 4 <;> exact Subsingleton.elim _ _
    rw [hc]
    exact herr u i hi
  exact long_padded_component_maps_from_frequencies hn hK F hF m d θ D hθ P π w wM raw true true eps lam hlam hlamθ heps N hpos' hmatch' herr'
end Oberwolfach
