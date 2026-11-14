module

public import Oberwolfach.OrdinaryBoundarySupportGeometry

@[expose] public section
/-! Class sizes and multiplicities depend only on the physical boundary
graph, rather than the much denser whole host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_class_boundary_degree_bounds
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (Dmax:ℕ)
    (hdeg:∀w:V⊕U,(ordinaryBoundaryGraph Q H X Z).degree w≤Dmax):
    (∀i,(ordinaryBoundaryRowSet H X Z i).card≤Dmax) ∧
    (∀j,(ordinaryBoundaryHubSet H Z X j).card≤Dmax) ∧
    (∀v,(Finset.univ.filter (fun i=>v∈ordinaryBoundaryRimSet Q X i)).card≤Dmax) ∧
    (∀z,(Finset.univ.filter (fun i=>z∈ordinaryBoundaryRowSet H X Z i)).card≤Dmax):=by
  let G:=ordinaryBoundaryGraph Q H X Z
  have hsupport:=ordinary_boundary_physical_supports_neighbor Q H X Z
  constructor
  · intro i
    have hsub:(ordinaryBoundaryRowSet H X Z i).image (Sum.inr:U→V⊕U)⊆G.neighborFinset (Sum.inl i.val):=by
      intro w hw
      have hh:=hsupport (Sum.inr i) (Finset.mem_union_right _ hw)
      exact hh
    have hh:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Sum.inr_injective,SimpleGraph.card_neighborFinset_eq_degree] at hh
    exact hh.trans (hdeg (Sum.inl i.val))
  constructor
  · intro j
    have hsub:(ordinaryBoundaryHubSet H Z X j).image (Sum.inl:V→V⊕U)⊆G.neighborFinset (Sum.inr j.val):=by
      intro w hw
      exact hsupport (Sum.inl j) hw
    have hh:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Sum.inl_injective,SimpleGraph.card_neighborFinset_eq_degree] at hh
    exact hh.trans (hdeg (Sum.inr j.val))
  constructor
  · intro v
    let C:Finset {x:V // x∉X}:=Finset.univ.filter (fun i=>v∈ordinaryBoundaryRimSet Q X i)
    have hsub:C.image (fun (i:{x:V // x∉X})=>(Sum.inl i.val:V⊕U))⊆G.neighborFinset (Sum.inl v):=by
      intro w hw
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hw
      have hv:v∈ordinaryBoundaryRimSet Q X i:=(Finset.mem_filter.mp hi).2
      have hmem:Sum.inl v∈ordinaryBoundaryPhysicalSupports Q H X Z (Sum.inr i):=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
      have hh:=hsupport (Sum.inr i) hmem
      apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp hh).symm
    have hinj:Function.Injective (fun i:{x:V // x∉X}=>(Sum.inl i.val:V⊕U)):=by
      intro a b hab
      exact Subtype.ext (Sum.inl.inj hab)
    have hh:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj,SimpleGraph.card_neighborFinset_eq_degree] at hh
    exact hh.trans (hdeg (Sum.inl v))
  · intro z
    let C:Finset {x:V // x∉X}:=Finset.univ.filter (fun i=>z∈ordinaryBoundaryRowSet H X Z i)
    have hsub:C.image (fun (i:{x:V // x∉X})=>(Sum.inl i.val:V⊕U))⊆G.neighborFinset (Sum.inr z):=by
      intro w hw
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hw
      have hz:z∈ordinaryBoundaryRowSet H X Z i:=(Finset.mem_filter.mp hi).2
      have hmem:Sum.inr z∈ordinaryBoundaryPhysicalSupports Q H X Z (Sum.inr i):=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
      have hh:=hsupport (Sum.inr i) hmem
      apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp hh).symm
    have hinj:Function.Injective (fun i:{x:V // x∉X}=>(Sum.inl i.val:V⊕U)):=by
      intro a b hab
      exact Subtype.ext (Sum.inl.inj hab)
    have hh:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj,SimpleGraph.card_neighborFinset_eq_degree] at hh
    exact hh.trans (hdeg (Sum.inr z))
end Oberwolfach
