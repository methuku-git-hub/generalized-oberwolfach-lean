module

public import Oberwolfach.PhysicalSampledMatchingRows

@[expose] public section
/-! Physical rim-degree and spoke-degree rows have at most one entry per
opposite vertex, so every row has size at most the host order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryPhysicalRowIndex (V U:Type):Type:=V⊕V⊕U

instance ordinaryPhysicalRowIndexFintype : Fintype (OrdinaryPhysicalRowIndex V U):=by
  unfold OrdinaryPhysicalRowIndex
  infer_instance

theorem ordinary_physical_row_index_card_le (hU:Fintype.card U≤Fintype.card V):
    Fintype.card (OrdinaryPhysicalRowIndex V U)≤3*Fintype.card V :=by
  simp only [OrdinaryPhysicalRowIndex,Fintype.card_sum]
  omega

def ordinaryPhysicalRow:OrdinaryPhysicalRowIndex V U→Finset (Sym2 V⊕(V×U))
  | Sum.inl v=>Finset.univ.image (fun x:V=>Sum.inl s(v,x))
  | Sum.inr (Sum.inl v)=>Finset.univ.image (fun u:U=>Sum.inr (v,u))
  | Sum.inr (Sum.inr u)=>Finset.univ.image (fun v:V=>Sum.inr (v,u))

theorem ordinary_physical_row_card_le (hU:Fintype.card U≤Fintype.card V)
    (r:OrdinaryPhysicalRowIndex V U):
    (ordinaryPhysicalRow r).card≤Fintype.card V :=by
  cases r with
  | inl v=>
    exact (Finset.card_image_le.trans_eq (Finset.card_univ)).trans (le_refl _)
  | inr r=>
    cases r with
    | inl v=>
      exact (Finset.card_image_le.trans_eq (Finset.card_univ)).trans hU
    | inr u=>
      exact (Finset.card_image_le.trans_eq (Finset.card_univ)).trans (le_refl _)

theorem physical_sampled_row_card_le
    {A:Type} [Fintype A] [DecidableEq A] (φ:A→Sym2 V⊕(V×U)) (σ:A→Bool)
    (hU:Fintype.card U≤Fintype.card V) (r:OrdinaryPhysicalRowIndex V U):
    (physicalSampledRow φ σ (ordinaryPhysicalRow r)).card≤Fintype.card V :=by
  let row:=physicalSampledRow φ σ (ordinaryPhysicalRow r)
  have himage:(row.image Subtype.val)⊆ordinaryPhysicalRow r:=by
    intro x hx
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hv).2
  have hh:=Finset.card_le_card himage
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh.trans (ordinary_physical_row_card_le hU r)
end Oberwolfach
