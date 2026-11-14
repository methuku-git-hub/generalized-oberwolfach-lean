module

public import Oberwolfach.LongRawMatchingRealizations
public import Oberwolfach.RealizationHubCounts

@[expose] public section
/-! The physical realization keeps the selected length class and hub counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawRealizedFrequencyDecidableEqFin1 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_realized_family_hub_count
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw g j ℓ)
    let key:=fun c:RestrictedResource (mixedCandidateResources R) e=>
      (c.val.1,longRawSeedHub π d m ℓ c.val.1 c.val.2)
    let key':=fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>
      (z.1,longRawRealizedHub P π d m raw g j ℓ z.1 z.2)
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
      Set.InjOn lift (↑M:Set _)→
      ∀i u,((M.image lift).filter (fun z=>key' z=(i,u))).card=
        (M.filter (fun c=>key c=(i,u))).card :=by
  intro state e R lift key key' M hinj i u
  apply realization_hub_count M lift key key' hinj ?_ (i,u)
  intro c hc
  apply Prod.ext
  · rfl
  · exact long_raw_matching_realization_preserves_hub P π d m raw g j ℓ c
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawRealizedFrequencyDecidableEqFin2 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_matching_realized_family_hub_count
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw g j ℓ)
    let key:=fun c:RestrictedResource (mixedCandidateResources R) e=>
      (c.val.1,longRawSeedHub π d m ℓ c.val.1 c.val.2)
    let key':=fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>
      (z.1,longRawRealizedHub P π d m raw g j ℓ z.1 z.2)
    ∀(w:∀i,longRawSeedFamilies (U:=U) π d m ℓ i→ℝ)
      (M:Finset (RestrictedResource (mixedCandidateResources R) e)),
    (∀i c,0<w i c→1≤(R i c).card) →
    (∀c∈M,0<mixedCandidateWeight w c.val) →
    (∀c∈M,∀d∈M,c≠d→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e d)) →
    ∀i u,((M.image lift).filter (fun z=>key' z=(i,u))).card=
      (M.filter (fun c=>key c=(i,u))).card :=by
  intro state e R lift key key' w M hsize hpos hmatch
  have hinj: Set.InjOn lift (↑M:Set _) :=
    (long_raw_matching_realizations P π d m raw g j ℓ w M hsize hpos hmatch).2
  exact long_raw_realized_family_hub_count P π d m raw g j ℓ M hinj
end Oberwolfach
