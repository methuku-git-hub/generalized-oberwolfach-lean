module

public import Oberwolfach.LongRawAbsoluteFrequencyAll
public import Oberwolfach.ClassFrequencyDomainError

@[expose] public section
/-! Positive-support matching selects no candidate at discarded hub-length pairs,
so the retained absolute frequency error holds at every pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawMatchingSizeFrequencyFinDecidable (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_matching_size_from_frequencies (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (m d:ℕ) (θ D:ℝ)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (ni:Fin K→ℕ) (hni:∀i,1≤ni i) (w:∀i,OrdinaryCycle P (ni i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (eps:ℝ)
    (heps:0≤eps):
    let ℓ:=fun i=>ni i+2
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let wO:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let wmix:=longMixedSeedWeight wM wO
    let hub:=fun c:RestrictedResource (mixedCandidateResources R) e=>longRawSeedHub π d m ℓ c.val.1 c.val.2
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,0<mixedCandidateWeight wmix c.val) →
    (∀u i, θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u →
      let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((ni i+2:ℕ):ℝ)
      |(((M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card:ℝ)-(1-θ)*t)|≤eps*n) →
    ∀u,
      |(∑i:Fin K,((ni i+2:ℕ):ℝ)*((M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card:ℝ)) -
         (1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)| ≤
      (eps*(n:ℝ))*(∑i:Fin K,((ni i+2:ℕ):ℝ)) :=by
  intro ℓ state e R wO wmix hub M hpos herr u
  have hall:=long_raw_absolute_frequency_all_classes hK F hF m d θ D P π ni hni w wM raw g j eps heps M hpos herr
  apply class_frequency_domain_error
  · intro i
    positivity
  · intro i
    have hi:=hall u i
    dsimp only at hi
    convert hi using 1
    congr 1
    dsimp [hub,ℓ]
    ring
end Oberwolfach
