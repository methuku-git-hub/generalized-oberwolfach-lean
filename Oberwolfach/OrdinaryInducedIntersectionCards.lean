module

public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! Neighbour and spoke intersections in finite induced domains are exactly
the corresponding ambient intersections with those domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_neighbor_intersection_card (Q:SimpleGraph V) (A X:Finset V) (v:A):
    (((Q.induce (A:Set V)).neighborFinset v)∩(Finset.univ.filter (fun w:A=>w.val∈X))).card=
      (Q.neighborFinset v.val∩(X∩A)).card:=by
  let S:=((Q.induce (A:Set V)).neighborFinset v)∩(Finset.univ.filter (fun w:A=>w.val∈X))
  have he:S.image (Subtype.val:A→V)=Q.neighborFinset v.val∩(X∩A):=by
    ext w
    simp only [S,Finset.mem_image,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,
      SimpleGraph.mem_neighborFinset,SimpleGraph.induce_adj]
    constructor
    · rintro ⟨z,⟨hz,hx⟩,rfl⟩
      exact ⟨hz,hx,z.property⟩
    · rintro ⟨hq,hx,ha⟩
      exact ⟨⟨w,ha⟩,⟨hq,hx⟩,rfl⟩
  have hh:=congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem ordinary_induced_spoke_intersection_card (H:V→U→Prop) (B Z:Finset U) (v:V):
    (Finset.univ.filter (fun u:B=>H v u.val ∧ u.val∈Z)).card=
      ((Finset.univ.filter (H v))∩(Z∩B)).card:=by
  let S:=Finset.univ.filter (fun u:B=>H v u.val ∧ u.val∈Z)
  have he:S.image (Subtype.val:B→U)=(Finset.univ.filter (H v))∩(Z∩B):=by
    ext u
    simp only [S,Finset.mem_image,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨z,⟨hz,hZ⟩,rfl⟩
      exact ⟨hz,hZ,z.property⟩
    · rintro ⟨hh,hZ,hB⟩
      exact ⟨⟨u,hB⟩,⟨hh,hZ⟩,rfl⟩
  have hh:=congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh
end Oberwolfach
