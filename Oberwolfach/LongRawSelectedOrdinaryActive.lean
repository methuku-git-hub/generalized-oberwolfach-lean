module

public import Oberwolfach.LongRawAssignedPartialGraphEmbeddings

@[expose] public section
/-! Every rim and spoke of an extracted selected ordinary wheel is active
in the same raw approximate outcome used to define its restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_selected_ordinary_resource_active
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    ∀a:LongRawSelectedOrdinary π d m ℓ e M,
    ∀v∈orderedOrdinaryResources (longRawSelectedOrdinaryWheel π d m ℓ e M a).val,
      state (ordinaryMarkedResourceEmbedding v)=true :=by
  intro state e R M a v hv
  let Q:=longRawSelectedOrdinaryWheel π d m ℓ e M a
  have hm:ordinaryMarkedResourceEmbedding v∈(orderedOrdinaryResources Q.val).map ordinaryMarkedResourceEmbedding:=
    Finset.mem_map.mpr ⟨v,hv,rfl⟩
  obtain ⟨z,hz⟩:=Q.property (ordinaryMarkedResourceEmbedding v) hm
  have hs:state (e z)=true:=by
    change state z.val=true
    exact (mem_bernoulliVertexSet state z.val).mp z.property
  simpa only [hz] using hs

theorem long_raw_selected_ordinary_rim_active
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    ∀a:LongRawSelectedOrdinary π d m ℓ e M,∀x y,
    longRawSelectedRimRelation π d m ℓ e M a x y→
      rawMarkedPairRims P π d raw (Sum.inl (x,y)) ∨
      rawMarkedPairRims P π d raw (Sum.inl (y,x)) :=by
  intro state e R M a x y h
  rcases h with ⟨i,h|h⟩
  · left
    have hv:Sum.inl (x,y)∈orderedOrdinaryResources (longRawSelectedOrdinaryWheel π d m ℓ e M a).val:=by
      apply (orderedOrdinaryResources_rim _ _).mpr
      exact ⟨i,Prod.ext h.1.symm h.2.symm⟩
    have hs:=long_raw_selected_ordinary_resource_active P π d m ℓ raw g j M a (Sum.inl (x,y)) hv
    simpa [state,longRawHubState,typedMarkedResourceState,ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] using hs
  · right
    have hv:Sum.inl (y,x)∈orderedOrdinaryResources (longRawSelectedOrdinaryWheel π d m ℓ e M a).val:=by
      apply (orderedOrdinaryResources_rim _ _).mpr
      exact ⟨i,Prod.ext h.1.symm h.2.symm⟩
    have hs:=long_raw_selected_ordinary_resource_active P π d m ℓ raw g j M a (Sum.inl (y,x)) hv
    simpa [state,longRawHubState,typedMarkedResourceState,ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] using hs
end Oberwolfach
