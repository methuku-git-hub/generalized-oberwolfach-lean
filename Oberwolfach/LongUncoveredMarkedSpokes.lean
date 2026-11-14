module

public import Oberwolfach.LongMatchedSpokeCovered
public import Oberwolfach.UncoveredSpokeIncidenceBound
public import Oberwolfach.LongRawSurvivingResourceState
public import Oberwolfach.SurvivingMatchingCoverageLift
public import Oberwolfach.LongRawIncidenceFamily

@[expose] public section
/-! The matching's uncovered incidence test controls uncovered marked spokes
at the same hub, even after the physical-edge deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longUncoveredMarkedSpokesFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_uncovered_marked_spokes_le_matching_incidence
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n))):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (w:U),
    let Marked:=longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w
    let Available:=Finset.univ.filter (fun v=>rawMarkedPairSpokes π d raw true true true v w)
    let Covered:=Finset.univ.filter (fun v=>∃W∈Marked,Sum.inr (v,w)∈markedWheelPhysicalResources W)
    (Available\Covered).card≤
      (longRawIncidenceSet S (.inr (true,.inr w))\M.biUnion Q).card:=by
  intro R T S hST q Q M w Marked Available Covered
  let Inc:=longRawIncidenceSet S (.inr (true,.inr w))
  let Matched:=M.biUnion Q
  let f:Fin n→LongRawHubResource n U:=fun v=>Sum.inr (true,v,w)
  have hf:Function.Injective f:=by intro x y h; simpa [f] using h
  have hinc:∀v∈Available,f v∈Inc.image Subtype.val:=by
    intro v hv
    have hvstate:rawMarkedPairSpokes π d raw true true true v w:=(Finset.mem_filter.mp hv).2
    have hvT:f v∈T:=by
      simp [T,f,longRawHubState,typedMarkedResourceState,bernoulliVertexSet,hvstate]
    have hvS:f v∈S:=long_raw_surviving_sample_spoke P π d raw true true Del (f v) hvT ⟨v,w,rfl⟩
    let x:{z // z∈S}:=⟨f v,hvS⟩
    have hx:x∈Inc:=by simp [Inc,longRawIncidenceSet,longRawResourceIncident,x,f]
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  have hcovered:∀v∈Available,f v∈Matched.image Subtype.val→v∈Covered:=by
    intro v hv hm
    obtain ⟨x,hx,hxval⟩:=Finset.mem_image.mp hm
    let emb:=survivingResourceEmbedding S T hST
    let xT:{z // z∈T}:=emb x
    have hLift:=surviving_candidate_covered_resources_lift R S T hST M
    have hxT:xT∈(M.map q).biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈T))):=by
      rw [hLift]
      exact Finset.mem_map.mpr ⟨x,hx,rfl⟩
    have hvW:=long_matched_true_spoke_covered_at_hub P π d m ℓ raw (M.map q) v w xT
      (by simpa [xT,emb,survivingResourceEmbedding,f] using hxval) hxT
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvW⟩
  have hbound:=uncovered_spoke_incidence_bound Available Covered (Inc.image Subtype.val) (Matched.image Subtype.val) f hf hinc hcovered
  have heq:(Inc.image Subtype.val\Matched.image Subtype.val).card=(Inc\Matched).card:=by
    rw [←Finset.image_sdiff Inc Matched Subtype.val_injective,Finset.card_image_of_injective _ Subtype.val_injective]
  rw [heq] at hbound
  exact hbound
end Oberwolfach
