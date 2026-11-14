module

public import Oberwolfach.LocalMatchingSpokeTests

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_local_vertex_spoke_incidence_card_le
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (g:Bool) (v:Fin n) (H:Finset U):
    (longLocalVertexSpokeIncidence S g v H).card≤H.card:=by
  let f:U→LongRawHubResource n U:=fun w=>Sum.inr (g,v,w)
  have hsub:(longLocalVertexSpokeIncidence S g v H).image Subtype.val⊆H.image f:=by
    intro z hz
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
    obtain ⟨w,hw,hwval⟩:=(Finset.mem_filter.mp hx).2
    exact Finset.mem_image.mpr ⟨w,hw,hwval.symm⟩
  have hh:=Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh.trans Finset.card_image_le

theorem long_local_hub_spoke_incidence_card_le
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (g:Bool) (w:U) (A:Finset (Fin n)):
    (longLocalHubSpokeIncidence S g w A).card≤A.card:=by
  let f:Fin n→LongRawHubResource n U:=fun v=>Sum.inr (g,v,w)
  have hsub:(longLocalHubSpokeIncidence S g w A).image Subtype.val⊆A.image f:=by
    intro z hz
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
    obtain ⟨v,hv,hvval⟩:=(Finset.mem_filter.mp hx).2
    exact Finset.mem_image.mpr ⟨v,hv,hvval.symm⟩
  have hh:=Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh.trans Finset.card_image_le
end Oberwolfach
