module

public import Oberwolfach.OrdinaryBoundarySupportExact

@[expose] public section
/-! Removing physical boundary edges shrinks each actual endpoint and hub
class, with the same outside-root indexing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem ordinary_boundary_classes_of_subgraph (Q Q':SimpleGraph V) (H H':V→U→Prop)
    (X:Finset V) (Z:Finset U) (hsub:ordinaryBoundaryGraph Q' H' X Z≤ordinaryBoundaryGraph Q H X Z):
    (∀j:{u:U // u∉Z},ordinaryBoundaryHubSet H' Z X j⊆ordinaryBoundaryHubSet H Z X j) ∧
    (∀i:{v:V // v∉X},ordinaryBoundaryRimSet Q' X i⊆ordinaryBoundaryRimSet Q X i) ∧
    (∀i:{v:V // v∉X},ordinaryBoundaryRowSet H' X Z i⊆ordinaryBoundaryRowSet H X Z i):=by
  have hs (i:{u:U // u∉Z}⊕{v:V // v∉X}):
      ordinaryBoundaryPhysicalSupports Q' H' X Z i⊆ordinaryBoundaryPhysicalSupports Q H X Z i:=by
    rw [ordinary_boundary_supports_eq_neighbors,ordinary_boundary_supports_eq_neighbors]
    intro w hw
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (hsub ((SimpleGraph.mem_neighborFinset _ _ _).mp hw))
  refine ⟨?_,?_,?_⟩
  · intro j v hv
    have hh:=hs (Sum.inl j) (show Sum.inl v∈ordinaryBoundaryPhysicalSupports Q' H' X Z (Sum.inl j) from
      Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    simpa [ordinaryBoundaryPhysicalSupports] using hh
  · intro i v hv
    have hh:=hs (Sum.inr i) (show Sum.inl v∈ordinaryBoundaryPhysicalSupports Q' H' X Z (Sum.inr i) from
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩))
    simpa [ordinaryBoundaryPhysicalSupports] using hh
  · intro i u hu
    have hh:=hs (Sum.inr i) (show Sum.inr u∈ordinaryBoundaryPhysicalSupports Q' H' X Z (Sum.inr i) from
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u,hu,rfl⟩))
    simpa [ordinaryBoundaryPhysicalSupports] using hh
end Oberwolfach
