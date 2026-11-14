module

public import Oberwolfach.PrescribedDependentPhysical
public import Oberwolfach.PrescribedSourceGraphSupport

@[expose] public section
/-! The graph of a separately typed source factor is mapped exactly into its
fiber in the common dependent-sum source universe. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

theorem prescribed_lifted_source_graph_eq_map (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I):
    prescribedSourceGraph (prescribedLiftDependentPieces Finset.univ.toList pieces) i =
      (prescribedDependentGraph pieces i).map (Sigma.mk i) := by
  ext u v
  constructor
  · intro huv
    have hu:=prescribed_source_graph_endpoint _ i u v huv
    have hv:=prescribed_source_graph_endpoint _ i v u huv.symm
    have hu':u.1=i:=prescribed_lifted_source_vertex_fiber pieces i u hu
    have hv':v.1=i:=prescribed_lifted_source_vertex_fiber pieces i v hv
    rcases u with ⟨j,x⟩
    rcases v with ⟨k,y⟩
    simp only at hu' hv'
    subst j
    subst k
    apply (SimpleGraph.map_adj ⟨Sigma.mk i,sigma_mk_injective⟩ (prescribedDependentGraph pieces i) _ _).mpr
    exact ⟨x,y,(prescribed_lifted_source_adjacency pieces i x y).mp huv,rfl,rfl⟩
  · intro huv
    obtain ⟨x,y,hxy,rfl,rfl⟩:=(SimpleGraph.map_adj ⟨Sigma.mk i,sigma_mk_injective⟩ (prescribedDependentGraph pieces i) u v).mp huv
    exact (prescribed_lifted_source_adjacency pieces i x y).mpr hxy
end Oberwolfach
