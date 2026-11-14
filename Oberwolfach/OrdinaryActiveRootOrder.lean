module

public import Oberwolfach.OrdinaryPairSupportReduction
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! The finite old vertex types have size bounded by the physical support,
not by the ambient host order. Isolated ambient labels are not included. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryActiveVertexEmbedding (G : SimpleGraph V) (H : V → U → Prop) :
    (OrdinaryActiveRow G⊕OrdinaryActiveHub H) ↪ {x : V⊕U // x∈(ordinaryPhysicalGraph G H).support} where
  toFun := fun x=>match x with
    | .inl v=>⟨.inl v.val,by obtain ⟨w,hw⟩:=v.property;exact ⟨.inl w,hw⟩⟩
    | .inr u=>⟨.inr u.val,by obtain ⟨v,hv⟩:=u.property;exact ⟨.inl v,hv⟩⟩
  inj' := by
    intro x y he
    have he' := congrArg Subtype.val he
    cases x with
    | inl x=>
      cases y with
      | inl y=>exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj he'))
      | inr y=>exact (Sum.inl_ne_inr he').elim
    | inr x=>
      cases y with
      | inl y=>exact (Sum.inr_ne_inl he').elim
      | inr y=>exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj he'))

theorem ordinary_active_root_order (G : SimpleGraph V) (H : V → U → Prop) :
    Fintype.card (OrdinaryActiveRow G)+Fintype.card (OrdinaryActiveHub H)≤
      (ordinaryPhysicalGraph G H).support.toFinset.card := by
  have hh := Fintype.card_le_of_injective _ (ordinaryActiveVertexEmbedding G H).injective
  simpa only [Fintype.card_sum,Set.toFinset_card] using hh

end Oberwolfach
