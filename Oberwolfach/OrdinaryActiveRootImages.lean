module

public import Oberwolfach.OrdinaryActiveRootOrder
public import Oberwolfach.OrdinaryResourceEndpointSets

@[expose] public section

/-! Exact old row and hub sets after removing isolated labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinaryActiveRow_image (G:SimpleGraph V) :
    Finset.univ.image (ordinaryActiveRowEmbedding G)=G.support.toFinset := by
  ext v
  constructor
  · intro hv
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv
    exact Set.mem_toFinset.mpr x.property
  · intro hv
    exact Finset.mem_image.mpr ⟨⟨v,Set.mem_toFinset.mp hv⟩,Finset.mem_univ _,rfl⟩

theorem ordinaryActiveHub_image (H:V→U→Prop) :
    Finset.univ.image (ordinaryActiveHubEmbedding H)=Finset.univ.filter (fun u=>∃ v,H v u) := by
  ext u
  constructor
  · intro hu
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.property⟩
  · intro hu
    exact Finset.mem_image.mpr ⟨⟨u,(Finset.mem_filter.mp hu).2⟩,Finset.mem_univ _,rfl⟩

theorem ordinary_resources_active_rows (G:SimpleGraph V) (H:V→U→Prop)
    (hbal:∀ v,G.degree v=2*(Finset.univ.filter (H v)).card) :
    ordinaryResourceRows (ordinaryHostResources G H)=G.support.toFinset := by
  apply Finset.Subset.antisymm
  · apply ordinaryResourceRows_subset
    · intro v w he
      have hG: G.Adj v w:=(ordinaryHostResources_rim G H _).mp he
      exact ⟨Set.mem_toFinset.mpr hG.mem_support_left,Set.mem_toFinset.mpr hG.mem_support_right⟩
    · intro v u he
      exact Set.mem_toFinset.mpr (balanced_spoke_row_support G H hbal v u ((ordinaryHostResources_spoke _ _ _ _).mp he))
  · intro v hv
    obtain ⟨w,hw⟩:=Set.mem_toFinset.mp hv
    exact Finset.mem_biUnion.mpr ⟨Sum.inl s(v,w),(ordinaryHostResources_rim _ _ _).mpr hw,by simp⟩

theorem ordinary_resources_active_hubs (G:SimpleGraph V) (H:V→U→Prop) :
    ordinaryResourceHubs (ordinaryHostResources G H)=Finset.univ.filter (fun u=>∃ v,H v u) := by
  apply Finset.Subset.antisymm
  · apply ordinaryResourceHubs_subset
    intro v u he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,(ordinaryHostResources_spoke _ _ _ _).mp he⟩
  · intro u hu
    obtain ⟨v,hv⟩:=(Finset.mem_filter.mp hu).2
    exact Finset.mem_biUnion.mpr ⟨Sum.inr (v,u),(ordinaryHostResources_spoke _ _ _ _).mpr hv,by simp⟩

end Oberwolfach
