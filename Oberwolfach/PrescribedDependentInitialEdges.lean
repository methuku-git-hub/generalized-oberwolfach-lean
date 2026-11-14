module

public import Oberwolfach.PrescribedDependentMaps
public import Oberwolfach.PrescribedDependentPhysical
public import Oberwolfach.PrescribedInducedEdgeRelabel

@[expose] public section
/-! The initially prescribed physical edges agree before and after
relabelling the source vertices into the dependent sum. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

def prescribedDependentInitialEdges (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (A:∀ i,Finset (X i)) (ψ:∀ i,X i→V) (i:I):Finset (Sym2 V):=
  (prescribedInducedSourceEdges (prescribedDependentGraph pieces i) (A i)).image (Sym2.map (ψ i))

theorem prescribed_lifted_initial_edges (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (A:∀ i,Finset (X i)) (ψ:∀ i,X i→V) (v₀:V) (i:I):
    (prescribedInducedSourceEdges
      (prescribedSourceGraph (prescribedLiftDependentPieces Finset.univ.toList pieces) i)
      (prescribedLiftedSet A i)).image (Sym2.map (prescribedLiftedMap v₀ ψ i))=
        prescribedDependentInitialEdges pieces A ψ i := by
  let f:X i↪Σ i,X i:=⟨Sigma.mk i,sigma_mk_injective⟩
  have hAdj:∀ x y,(prescribedSourceGraph (prescribedLiftDependentPieces Finset.univ.toList pieces) i).Adj (f x) (f y) ↔
      (prescribedDependentGraph pieces i).Adj x y:=prescribed_lifted_source_adjacency pieces i
  have hEq:=prescribed_induced_source_edges_relabel (prescribedDependentGraph pieces i)
    (prescribedSourceGraph (prescribedLiftDependentPieces Finset.univ.toList pieces) i) f hAdj (A i)
  change (prescribedInducedSourceEdges _ ((A i).image f)).image _ = _
  rw [hEq,Finset.image_image]
  have hmap:(prescribedLiftedMap v₀ ψ i) ∘ f=ψ i:=by
    funext x
    exact prescribed_lifted_map_value v₀ ψ i x
  have hmap':Sym2.map (prescribedLiftedMap v₀ ψ i) ∘ Sym2.map f=Sym2.map (ψ i):=by
    rw [←Sym2.map_comp,hmap]
  rw [hmap']
  rfl
end Oberwolfach
