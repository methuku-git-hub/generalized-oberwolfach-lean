module

public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! A physical forbidden graph bounds separately the deleted spoke rows
and columns, without a factor depending on the sampling density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem physical_spoke_deleted_row (D : SimpleGraph (V⊕U)) (v : V) :
    (Finset.univ.filter (fun u=>D.Adj (Sum.inl v) (Sum.inr u))).card≤D.degree (Sum.inl v) := by
  let A:=Finset.univ.filter (fun u=>D.Adj (Sum.inl v) (Sum.inr u))
  have hs : A.image Sum.inr⊆D.neighborFinset (Sum.inl v) := by
    intro z hz
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Finset.mem_filter.mp hu).2
  have he : (A.image (Sum.inr:U→V⊕U)).card=A.card := Finset.card_image_of_injective _ Sum.inr_injective
  have hh:=Finset.card_le_card hs
  rw [he,SimpleGraph.card_neighborFinset_eq_degree] at hh
  exact hh

theorem physical_spoke_deleted_col (D : SimpleGraph (V⊕U)) (u : U) :
    (Finset.univ.filter (fun v=>D.Adj (Sum.inl v) (Sum.inr u))).card≤D.degree (Sum.inr u) := by
  let A:=Finset.univ.filter (fun v=>D.Adj (Sum.inl v) (Sum.inr u))
  have hs : A.image Sum.inl⊆D.neighborFinset (Sum.inr u) := by
    intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Finset.mem_filter.mp hv).2.symm
  have he : (A.image (Sum.inl:V→V⊕U)).card=A.card := Finset.card_image_of_injective _ Sum.inl_injective
  have hh:=Finset.card_le_card hs
  rw [he,SimpleGraph.card_neighborFinset_eq_degree] at hh
  exact hh

end Oberwolfach
