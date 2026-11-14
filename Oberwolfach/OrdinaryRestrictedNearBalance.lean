module

public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! Restricting an exactly balanced rim--spoke host away from two small sets
leaves a quantitatively near-balanced host on the remaining types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_restricted_near_balance (Q:SimpleGraph V) (H:V→U→Prop) (T:Finset V) (W:Finset U)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card):
    let Vfree:=Finset.univ\T;let Ufree:=Finset.univ\W;
    ∀v:Vfree,|(((Q.induce (Vfree:Set V)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u:Ufree=>H v.val u.val)).card|≤(T.card:ℝ)+2*W.card:=by
  intro Vfree Ufree v
  let N:=Q.neighborFinset v.val
  let S:=Finset.univ.filter (H v.val)
  have hdeg:(Q.induce (Vfree:Set V)).degree v=(N\T).card:=by
    rw [induced_degree_intersection]
    congr 1
    ext w
    simp [N,Vfree,Finset.mem_sdiff,Finset.mem_inter]
  have hrow:(Finset.univ.filter (fun u:Ufree=>H v.val u.val)).card=(S\W).card:=by
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
    exact hh
  have hN:=Finset.card_sdiff_add_card_inter N T
  have hS:=Finset.card_sdiff_add_card_inter S W
  have hNT:(N∩T).card≤T.card:=Finset.card_le_card Finset.inter_subset_right
  have hSW:(S∩W).card≤W.card:=Finset.card_le_card Finset.inter_subset_right
  have hQ:((N\T).card:ℝ)+(N∩T).card=Q.degree v.val:=by
    exact_mod_cast hN
  have hH:((S\W).card:ℝ)+(S∩W).card=(Finset.univ.filter (H v.val)).card:=by
    exact_mod_cast hS
  have hQr:(Q.degree v.val:ℝ)=2*(Finset.univ.filter (H v.val)).card:=by exact_mod_cast hbal v.val
  have hNT':((N∩T).card:ℝ)≤T.card:=by exact_mod_cast hNT
  have hSW':((S∩W).card:ℝ)≤W.card:=by exact_mod_cast hSW
  have hNT0:(0:ℝ)≤(N∩T).card:=by positivity
  have hSW0:(0:ℝ)≤(S∩W).card:=by positivity
  rw [hdeg,hrow]
  apply abs_le.mpr
  constructor <;> linarith only [hQ,hH,hQr,hNT',hSW',hNT0,hSW0]
end Oberwolfach
