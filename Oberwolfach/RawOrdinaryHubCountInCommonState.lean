module

public import Oberwolfach.SampledResourceSubsetCard
public import Oberwolfach.RetainedCommonHubCard
public import Oberwolfach.RawVariableSpokeHubCounts
public import Oberwolfach.MarkedExpandedApproximateProjection

@[expose] public section
/-! The ordinary hub test in the common typed state has precisely the
original raw ordinary-spoke count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_ordinary_common_hub_sample_count
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (g:Γ) (j:Color) (u:U):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)
    (((ordinaryCommonHubSpokeRoots u).filter (fun x=>state x=true)).card:ℝ)=
      rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) g j false u Finset.univ :=by
  intro state
  let f:V↪(((V×V)⊕(V×V))⊕(Bool×V×U)):=
    ⟨fun v=>Sum.inr (false,v,u),by intro x y h;exact congrArg Prod.fst (congrArg Prod.snd (Sum.inr.inj h))⟩
  let A:=Finset.univ.filter (fun v=>rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j false v u)
  have himage:(ordinaryCommonHubSpokeRoots u).filter (fun x=>state x=true)=A.image f:=by
    ext x
    constructor
    · intro hx
      obtain ⟨hxS,hxstate⟩:=Finset.mem_filter.mp hx
      unfold ordinaryCommonHubSpokeRoots ordinaryHubSpokeRoots at hxS
      obtain ⟨z,hz,hzx⟩:=Finset.mem_map.mp hxS
      have hv:∃v,z=Sum.inr (v,u):=by
        simpa only [Finset.mem_image,Finset.mem_univ,true_and,eq_comm] using hz
      obtain ⟨v,rfl⟩:=hv
      have hxf:x=f v:=by simpa [f,ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] using hzx.symm
      have hvH:rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j false v u:=by
        simpa [hxf,state,f,typedMarkedResourceState,rawMarkedPairSpokes] using hxstate
      exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvH⟩,hxf.symm⟩
    · intro hx
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
      have hvH:rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j false v u:=(Finset.mem_filter.mp hv).2
      apply Finset.mem_filter.mpr
      constructor
      · unfold ordinaryCommonHubSpokeRoots ordinaryHubSpokeRoots
        apply Finset.mem_map.mpr
        refine ⟨Sum.inr (v,u),?_,?_⟩
        · simpa only [Finset.mem_image,Finset.mem_univ,true_and] using (show ∃x:V,Sum.inr (x,u)=(Sum.inr (v,u): (V×V)⊕(V×U)) from ⟨v,rfl⟩)
        · rfl
      · simpa [state,f,typedMarkedResourceState,rawMarkedPairSpokes] using hvH
  have hc:=congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ f.injective] at hc
  rw [raw_spoke_hub_count_eq_card]
  exact_mod_cast hc
theorem expanded_raw_ordinary_common_hub_sample_count
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g:Γ) (j:Color) (u:U):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    (((ordinaryCommonHubSpokeRoots u).filter (fun x=>state x=true)).card:ℝ)=
      rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) g j false u Finset.univ :=by
  intro raw state
  have h:=raw_ordinary_common_hub_sample_count P π d raw g j u
  simpa only [state,raw,rawExpandedApproximateCollapse,id_eq] using h
end Oberwolfach
