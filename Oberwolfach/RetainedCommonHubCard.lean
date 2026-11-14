module

public import Oberwolfach.LongMixedHubSpokeCounts
public import Oberwolfach.RestrictedResourceSubsetCounts
public import Oberwolfach.MarkedRetainedResourceState

@[expose] public section
/-! The ordinary hub-spoke test set in the sampled resource ground has
exactly one element for each actually retained ordinary spoke. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem retained_common_ordinary_hub_card
    (R:(V×V)⊕(V×V)→Prop) (H:Bool→V→U→Prop) (u:U):
    let state:=typedMarkedResourceState R H
    let e: {a // a∈bernoulliVertexSet state} ↪ (((V×V)⊕(V×V))⊕(Bool×V×U)):=
      Function.Embedding.subtype _
    ((restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card:ℕ)=
      (Finset.univ.filter (fun v=>H false v u)).card := by
  intro state e
  let A:=Finset.univ.filter (fun v=>H false v u)
  let f:V↪(((V×V)⊕(V×V))⊕(Bool×V×U)):=
    ⟨fun v=>Sum.inr (false,v,u),by intro x y h;exact congrArg Prod.fst (congrArg Prod.snd (Sum.inr.inj h))⟩
  have himage:(restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).image e = A.image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hz
      have haS:(a.val)∈ordinaryCommonHubSpokeRoots u := (Finset.mem_filter.mp ha).2
      unfold ordinaryCommonHubSpokeRoots ordinaryHubSpokeRoots at haS
      obtain ⟨s,hs,hse⟩:=Finset.mem_map.mp haS
      obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hs
      have hz' : a.val=Sum.inr (false,v,u) := by simpa [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] using hse.symm
      have hstate : state a.val=true := (mem_bernoulliVertexSet state a.val).mp a.property
      have hv:H false v u := by simpa [state,hz',typedMarkedResourceState] using hstate
      exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,by simpa [f,e] using hz'.symm⟩
    · intro hz
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      have hvH:H false v u:=(Finset.mem_filter.mp hv).2
      have ha: f v∈bernoulliVertexSet state := by
        apply (mem_bernoulliVertexSet state (f v)).mpr
        simpa [state,f,typedMarkedResourceState] using hvH
      refine Finset.mem_image.mpr ⟨⟨f v,ha⟩,?_,rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      unfold ordinaryCommonHubSpokeRoots ordinaryHubSpokeRoots
      apply Finset.mem_map.mpr
      refine ⟨Sum.inr (v,u),?_,?_⟩
      · exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
      · rfl
  have hcard:=congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ e.injective,Finset.card_image_of_injective _ f.injective] at hcard
  exact hcard
end Oberwolfach
