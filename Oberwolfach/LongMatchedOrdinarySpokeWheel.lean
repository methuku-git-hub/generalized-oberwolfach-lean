module

public import Oberwolfach.LongMatchedSpokeCovered

@[expose] public section
/-! A covered ordinary spoke belongs to one of the actual matched wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longMatchedOrdinarySpokeFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_matched_ordinary_spoke_wheel
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool):
    let state:=longRawHubState P π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let Q:=restrictedResourceSet (mixedCandidateResources R) e
    ∀(M:Finset (RestrictedResource (mixedCandidateResources R) e)) (v:Fin n) (w:U)
      (x:{z // z∈bernoulliVertexSet state}),
      x.val=Sum.inr (false,v,w)→x∈M.biUnion Q→
      (∃a:LongRawSelectedOrdinary π d m ℓ e M,
        (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2=w ∧
        v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val)) ∨
      (∃W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true M w,
        ∃i:Fin (m+1),W.1.val i=v):=by
  intro state e R Q M v w x hx hmatched
  obtain ⟨c,hc,hxQ⟩:=Finset.mem_biUnion.mp hmatched
  let φ:{z // z∈bernoulliVertexSet state}→Finset (Fin n)⊕(Fin n×U):=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw true true z)
  let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw true true ℓ)
  let B:=longRawRealizedPhysicalResources P π d m raw true true ℓ
  have hphys:=mixed_restricted_physical_lift_resources R e φ (longRawRealizeComponent P π d m raw true true ℓ)
    B (long_raw_realize_component_resources P π d m raw true true ℓ) c
  have hφ:φ x=Sum.inr (v,w):=by
    simp [φ,markedRawSampledPhysicalEmbedding,typedResourcePhysical,markedResourceTypeEquiv,physicalResourceToFinite,hx]
  have hspoke:Sum.inr (v,w)∈B (lift c).1 (lift c).2:=by
    have hh:φ x∈(Q c).image φ:=Finset.mem_image.mpr ⟨x,hxQ,rfl⟩
    rw [←hphys,hφ] at hh
    exact hh
  cases htype:c.val.1 with
  | none =>
    let a:LongRawSelectedMarked π d m ℓ e M:=⟨c,hc,htype⟩
    let W:=longRawSelectedMarkedWheel P π d m ℓ raw true true M a
    have hW:=long_raw_selected_marked_realized_resources P π d m ℓ raw true true M a
    have hdec:longMatchedOrdinarySpokeFin n=instDecidableEqFin n:=Subsingleton.elim _ _
    rw [←hdec] at hW
    change B (lift c).1 (lift c).2=markedWheelPhysicalResources W at hW
    rw [hW] at hspoke
    obtain ⟨hw,hrim⟩:=(markedWheelPhysicalResources_spoke W v w).mp hspoke
    right
    refine ⟨W,?_,?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,rfl⟩
    · obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hrim
      exact ⟨j,hj⟩
  | some i =>
    let a:LongRawSelectedOrdinary π d m ℓ e M:=⟨c,hc,by simp [htype]⟩
    let W:=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val
    have hW:=long_raw_selected_ordinary_realized_resources P π d m ℓ raw true true M a
    change B (lift c).1 (lift c).2=ordinaryWheelPhysicalResources W at hW
    rw [hW] at hspoke
    have hex:∃i, W.1.val i=v ∧ W.2=w:=by
      simpa [ordinaryWheelPhysicalResources] using hspoke
    obtain ⟨j,hv,hw⟩:=hex
    left
    refine ⟨a,hw,?_⟩
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hv⟩
end Oberwolfach
