module

public import Oberwolfach.LongRawIncidenceFamily

@[expose] public section
/-! Unused ordinary spokes inject into both matching incidence defects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_unused_spoke_incidence_bounds
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (covered:Finset S)
    (unused:U→Finset (Fin n))
    (hunused:∀w v,v∈unused w→∃x:S,x.val=Sum.inr (false,v,w) ∧ x∉covered):
    (∀w,(unused w).card≤(longRawIncidenceSet S (.inr (false,.inr w))\covered).card) ∧
    (∀v,(Finset.univ.filter (fun w=>v∈unused w)).card≤
      (longRawIncidenceSet S (.inr (false,.inl v))\covered).card):=by
  constructor
  · intro w
    let f:Fin n→LongRawHubResource n U:=fun v=>Sum.inr (false,v,w)
    have hf:Function.Injective f:=by intro a b h;cases h;rfl
    have hsub:(unused w).image f⊆(longRawIncidenceSet S (.inr (false,.inr w))\covered).image Subtype.val:=by
      intro z hz
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      obtain ⟨x,hx,hxc⟩:=hunused w v hv
      refine Finset.mem_image.mpr ⟨x,?_,hx⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨?_,hxc⟩
      simp [longRawIncidenceSet,longRawResourceIncident,hx]
    have hcard:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hf] at hcard
    exact hcard.trans Finset.card_image_le
  · intro v
    let f:U→LongRawHubResource n U:=fun w=>Sum.inr (false,v,w)
    have hf:Function.Injective f:=by intro a b h;cases h;rfl
    have hsub:(Finset.univ.filter (fun w=>v∈unused w)).image f⊆
        (longRawIncidenceSet S (.inr (false,.inl v))\covered).image Subtype.val:=by
      intro z hz
      obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hz
      obtain ⟨x,hx,hxc⟩:=hunused w v (Finset.mem_filter.mp hw).2
      refine Finset.mem_image.mpr ⟨x,?_,hx⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨?_,hxc⟩
      simp [longRawIncidenceSet,longRawResourceIncident,hx]
    have hcard:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hf] at hcard
    exact hcard.trans Finset.card_image_le
end Oberwolfach
