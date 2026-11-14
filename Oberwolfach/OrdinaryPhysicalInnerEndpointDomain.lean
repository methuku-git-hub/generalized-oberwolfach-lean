module

public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! The fixed physical inner domain contains every rim and spoke endpoint
class, before the fresh physical-edge sample is exposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryPhysicalInnerDomain (A:Finset V) (Z:Finset U):Finset (V⊕U):=
  (A.image Sum.inl)∪(Z.image Sum.inr)

theorem ordinary_physical_inner_endpoint_domains (Q:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (Z:Finset U):
    (∀i:{v:V // v∉A},(ordinaryBoundaryRimSet Q A i).image (Sum.inl:V→V⊕U)⊆ordinaryPhysicalInnerDomain A Z) ∧
    (∀i:{v:V // v∉A},(ordinaryBoundaryRowSet H A Z i).image (Sum.inr:U→V⊕U)⊆ordinaryPhysicalInnerDomain A Z):=by
  constructor
  · intro i x hx
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
    have hvA:v∈A:=(Finset.mem_inter.mp hv).2
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hvA,rfl⟩)
  · intro i x hx
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hx
    have huZ:u∈Z:=(Finset.mem_filter.mp hu).1
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u,huZ,rfl⟩)

theorem ordinary_physical_inner_domain_card (A:Finset V) (Z:Finset U):
    (ordinaryPhysicalInnerDomain A Z).card=A.card+Z.card:=by
  have hd:Disjoint (A.image (Sum.inl:V→V⊕U)) (Z.image (Sum.inr:U→V⊕U)):=by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨u,_,hu⟩:=Finset.mem_image.mp hy
    cases hu
  rw [ordinaryPhysicalInnerDomain,Finset.card_union_of_disjoint hd]
  simp only [Finset.card_image_of_injective _ Sum.inl_injective,Finset.card_image_of_injective _ Sum.inr_injective]
end Oberwolfach
