module

public import Oberwolfach.OrdinaryRestrictedNearBalance

@[expose] public section
/-! Removing hub roots loses at most their number from each spoke row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_spoke_degree
    (H:V→U→Prop) (T:Finset V) (W:Finset U) (β βfree:ℝ)
    (hdegree:∀v,β*Fintype.card V≤((Finset.univ.filter (H v)).card:ℝ))
    (hbudget:βfree*Fintype.card ↥(Finset.univ\T)+(W.card:ℝ)≤β*Fintype.card V):
    let Vfree:=Finset.univ\T;let Ufree:=Finset.univ\W;
    ∀v:Vfree,βfree*Fintype.card Vfree≤((Finset.univ.filter (fun u:Ufree=>H v.val u.val)).card:ℝ):=by
  intro Vfree Ufree v
  let S:=Finset.univ.filter (H v.val)
  let A:=Finset.univ.filter (fun u:Ufree=>H v.val u.val)
  have he:A.image (Subtype.val:Ufree→U)=S\W:=by
    ext u
    simp only [A,S,Ufree,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨hx,(Finset.mem_sdiff.mp x.property).2⟩
    · rintro ⟨hu,huW⟩
      exact ⟨⟨u,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,huW⟩⟩,hu,rfl⟩
  have hh:=congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  have hs:=Finset.card_sdiff_add_card_inter S W
  have hi:(S∩W).card≤W.card:=Finset.card_le_card Finset.inter_subset_right
  have hs':((S\W).card:ℝ)+(S∩W).card=S.card:=by exact_mod_cast hs
  have hi':((S∩W).card:ℝ)≤W.card:=by exact_mod_cast hi
  have hd:=hdegree v.val
  change β*Fintype.card V≤(S.card:ℝ) at hd
  change βfree*Fintype.card Vfree+(W.card:ℝ)≤β*Fintype.card V at hbudget
  change βfree*Fintype.card Vfree≤(A.card:ℝ)
  rw [hh]
  linarith
end Oberwolfach
