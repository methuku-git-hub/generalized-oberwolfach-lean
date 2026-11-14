module

public import Oberwolfach.LongRawAssignmentFromAbsoluteFrequency

@[expose] public section
/-! For every retained hub the padded seed length is its true component
length, so the sampled matching estimate supplies the component assignment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longPaddedAssignmentFinDecidable (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_padded_ordinary_assignment_from_absolute_frequency (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (m d:ℕ) (θ D:ℝ)
    (hθ:0<θ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (w:∀i,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (eps lam:ℝ)
    (hlam:0≤lam) (hlamθ:lam≤θ) (heps:eps≤lam*(θ/(100*(K:ℝ)^2))):
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let ℓ:=fun i=>ni i+2
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let wO:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let wmix:=longMixedSeedWeight wM wO
    let hub:=fun c:RestrictedResource (mixedCandidateResources R) e=>longRawSeedHub π d m ℓ c.val.1 c.val.2
    let idx:=fun c:RestrictedResource (mixedCandidateResources R) e=>c.val.1.getD ⟨0,hK⟩
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,0<mixedCandidateWeight wmix c.val) →
    (∀u i, θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u →
      let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((ni i+2:ℕ):ℝ)
      |(((M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card:ℝ)-(1-θ)*t)|≤eps*n) →
    ∃h:{c // c∈M.filter (fun c=>c.val.1.isSome)}↪(Σu,(F u).ConnectedComponent),
      ∀c,(h c).1=hub c.val ∧ Fintype.card (h c).2=(idx c.val).val+1 :=by
  intro ni hni ℓ state e R wO wmix hub idx M hpos herr
  apply long_raw_ordinary_assignment_from_absolute_frequency hn hK F hF m d θ D hθ.le P π ni hni w wM raw g j eps lam hlam hlamθ heps M hpos
  intro u i hf
  have hlen:=long_retained_hub_padded_length_exact F hF θ hθ i u hf
  simpa only [ni,hlen] using herr u i hf
end Oberwolfach
