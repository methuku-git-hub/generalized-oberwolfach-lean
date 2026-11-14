module

public import Oberwolfach.LongMixedTrueSpokeOnlyMarked
public import Oberwolfach.LongRawRealizationsAvoidAbsorber

@[expose] public section
/-! Every true marked spoke covered by the mixed matching is covered by one
of the actual marked wheels at its own hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longMatchedSpokeDecidableFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_matched_true_spoke_covered_at_hub
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool):
    let state:=longRawHubState P π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let Q:=restrictedResourceSet (mixedCandidateResources R) e
    ∀(M:Finset (RestrictedResource (mixedCandidateResources R) e)) (v:Fin n) (w:U)
      (x:{z // z∈bernoulliVertexSet state}),
      x.val=Sum.inr (true,v,w)→x∈M.biUnion Q→
      ∃W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true M w,
        Sum.inr (v,w)∈markedWheelPhysicalResources W:=by
  intro state e R Q M v w x hx hmatched
  obtain ⟨c,hc,hxQ⟩:=Finset.mem_biUnion.mp hmatched
  have hxR:Sum.inr (true,v,w)∈mixedCandidateResources R c.val:=by
    have hh: e x∈mixedCandidateResources R c.val:=(restrictedResourceSet_mem _ _ _ _).mp hxQ
    simpa [e,hx] using hh
  have hnone:c.val.1=none:=long_mixed_true_spoke_only_marked π d m ℓ c.val v w hxR
  let a:LongRawSelectedMarked π d m ℓ e M:=⟨c,hc,hnone⟩
  let W:=longRawSelectedMarkedWheel P π d m ℓ raw true true M a
  let φ:{z // z∈bernoulliVertexSet state}→Finset (Fin n)⊕(Fin n×U):=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw true true z)
  let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw true true ℓ)
  let B:=longRawRealizedPhysicalResources P π d m raw true true ℓ
  have hphys:=mixed_restricted_physical_lift_resources R e φ (longRawRealizeComponent P π d m raw true true ℓ)
    B (long_raw_realize_component_resources P π d m raw true true ℓ) c
  have hW:=long_raw_selected_marked_realized_resources P π d m ℓ raw true true M a
  have hdec:longMatchedSpokeDecidableFin n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [←hdec] at hW
  change B (lift c).1 (lift c).2=markedWheelPhysicalResources W at hW
  have hφ:φ x=Sum.inr (v,w):=by
    simp [φ,markedRawSampledPhysicalEmbedding,typedResourcePhysical,markedResourceTypeEquiv,physicalResourceToFinite,hx]
  have hspoke:Sum.inr (v,w)∈markedWheelPhysicalResources W:=by
    have hh:φ x∈(Q c).image φ:=Finset.mem_image.mpr ⟨x,hxQ,rfl⟩
    rw [←hphys,hW,hφ] at hh
    exact hh
  have hwheel:W.2.val=w:=(markedWheelPhysicalResources_spoke W v w).mp hspoke |>.1
  refine ⟨W,?_,hspoke⟩
  apply Finset.mem_image.mpr
  refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwheel⟩,rfl⟩
end Oberwolfach
