module

public import Oberwolfach.FullFactorSetPackingToDecomposition

@[expose] public section
/-! The set-valued physical edges used by marked reconstruction are exactly
the finset-valued edge images used by prescribed family embeddings. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem partial_factor_physical_set_eq_edge_image
    {X Y:Type*} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (F:SimpleGraph X) (f:X→Y) :
    partialFactorPhysicalEdgesPoly X F f = ↑(F.edgeFinset.image (Sym2.map f)) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨x,y,hxy,rfl⟩:=he
    exact Finset.mem_image.mpr ⟨s(x,y),SimpleGraph.mem_edgeFinset.mpr hxy,by rfl⟩
  · intro he
    exact mapped_edge_finset_mem_physical_set F f e he

theorem partial_factor_sets_disjoint_of_edge_finsets
    {X₁ X₂ Y:Type*} [Fintype X₁] [Fintype X₂] [DecidableEq X₁] [DecidableEq X₂] [DecidableEq Y]
    (F₁:SimpleGraph X₁) (F₂:SimpleGraph X₂) (f₁:X₁→Y) (f₂:X₂→Y)
    (hdis:Disjoint (F₁.edgeFinset.image (Sym2.map f₁)) (F₂.edgeFinset.image (Sym2.map f₂))) :
    Disjoint (partialFactorPhysicalEdgesPoly X₁ F₁ f₁) (partialFactorPhysicalEdgesPoly X₂ F₂ f₂) := by
  rw [partial_factor_physical_set_eq_edge_image,partial_factor_physical_set_eq_edge_image]
  exact Finset.disjoint_coe.mpr hdis
end Oberwolfach
