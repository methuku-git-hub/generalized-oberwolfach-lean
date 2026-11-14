module

public import Oberwolfach.LongUnusedSpokeIncidence

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def longLocalHubSpokeDefects {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (covered:Finset S) (g:Bool) (w:U) (A:Finset (Fin n)) : Finset S :=
  (longRawIncidenceSet S (.inr (g,.inr w))\covered).filter (fun z=>∃v∈A,z.val=Sum.inr (g,v,w))

def longLocalVertexSpokeDefects {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (covered:Finset S) (g:Bool) (v:Fin n) (H:Finset U) : Finset S :=
  (longRawIncidenceSet S (.inr (g,.inl v))\covered).filter (fun z=>∃w∈H,z.val=Sum.inr (g,v,w))

theorem long_unused_spoke_local_incidence_bounds
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (covered:Finset S) (g:Bool)
    (unused:U→Finset (Fin n)) (H:Finset U) (A:Finset (Fin n))
    (hunused:∀w v,v∈unused w→∃x:S,x.val=Sum.inr (g,v,w) ∧ x∉covered):
    (∀w,((unused w∩A).card)≤(longLocalHubSpokeDefects S covered g w A).card) ∧
    (∀v,(H.filter (fun w=>v∈unused w)).card≤(longLocalVertexSpokeDefects S covered g v H).card):=by
  constructor
  · intro w
    let f:Fin n→LongRawHubResource n U:=fun v=>Sum.inr (g,v,w)
    have hf:Function.Injective f:=by intro a b h;cases h;rfl
    have hsub:(unused w∩A).image f⊆(longLocalHubSpokeDefects S covered g w A).image Subtype.val:=by
      intro z hz
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      obtain ⟨x,hx,hxc⟩:=hunused w v (Finset.mem_inter.mp hv).1
      refine Finset.mem_image.mpr ⟨x,?_,hx⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨?_,hxc⟩,⟨v,(Finset.mem_inter.mp hv).2,hx⟩⟩
      simp [longRawIncidenceSet,longRawResourceIncident,hx]
    have hcard:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hf] at hcard
    exact hcard.trans Finset.card_image_le
  · intro v
    let f:U→LongRawHubResource n U:=fun w=>Sum.inr (g,v,w)
    have hf:Function.Injective f:=by intro a b h;cases h;rfl
    have hsub:(H.filter (fun w=>v∈unused w)).image f⊆(longLocalVertexSpokeDefects S covered g v H).image Subtype.val:=by
      intro z hz
      obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hz
      obtain ⟨x,hx,hxc⟩:=hunused w v (Finset.mem_filter.mp hw).2
      refine Finset.mem_image.mpr ⟨x,?_,hx⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨?_,hxc⟩,⟨w,(Finset.mem_filter.mp hw).1,hx⟩⟩
      simp [longRawIncidenceSet,longRawResourceIncident,hx]
    have hcard:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hf] at hcard
    exact hcard.trans Finset.card_image_le
end Oberwolfach
