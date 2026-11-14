module

public import Oberwolfach.PrescribedDependentSourceModel

@[expose] public section
/-! Relabelling separately typed source pieces preserves their physical
undirected edges and source-graph adjacency. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

def prescribedDependentPhysical (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I):Set (Sym2 (X i)):=
  {e | ∃ p∈pieces i,e∈p.edges}

def prescribedDependentGraph (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I):SimpleGraph (X i):=
  SimpleGraph.fromEdgeSet (prescribedDependentPhysical pieces i)

theorem prescribed_lifted_physical_membership (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (i:I) (e:Sym2 (X i)):
    Sym2.map (Sigma.mk i) e∈prescribedSourcePhysical (prescribedLiftDependentPieces Finset.univ.toList pieces) i ↔
      e∈prescribedDependentPhysical pieces i := by
  constructor
  · rintro ⟨p,hp,hpi,he⟩
    obtain ⟨j,hj,hp⟩:=List.mem_flatMap.mp hp
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
    simp only at hpi
    subst j
    rw [prescribed_piece_map_edges] at he
    obtain ⟨e',he',heq⟩:=Finset.mem_image.mp he
    have heq':e'=e:=Sym2.map.injective sigma_mk_injective heq
    subst e'
    exact ⟨q,hq,he'⟩
  · rintro ⟨q,hq,he⟩
    refine ⟨(i,q.map (Sigma.mk i)),?_,rfl,?_⟩
    · apply List.mem_flatMap.mpr
      exact ⟨i,by simp,List.mem_map.mpr ⟨q,hq,rfl⟩⟩
    · rw [prescribed_piece_map_edges]
      exact Finset.mem_image.mpr ⟨e,he,rfl⟩

theorem prescribed_lifted_source_adjacency (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (i:I) (x y:X i):
    (prescribedSourceGraph (prescribedLiftDependentPieces Finset.univ.toList pieces) i).Adj (Sigma.mk i x) (Sigma.mk i y) ↔
      (prescribedDependentGraph pieces i).Adj x y := by
  change (SimpleGraph.fromEdgeSet _).Adj (Sigma.mk i x) (Sigma.mk i y) ↔ (SimpleGraph.fromEdgeSet _).Adj x y
  rw [SimpleGraph.fromEdgeSet_adj,SimpleGraph.fromEdgeSet_adj]
  have he:s(Sigma.mk i x,Sigma.mk i y)=Sym2.map (Sigma.mk i) s(x,y):=rfl
  rw [he,prescribed_lifted_physical_membership]
  constructor
  · rintro ⟨he,hne⟩
    exact ⟨he,fun h=>hne (by simpa [h])⟩
  · rintro ⟨he,hne⟩
    exact ⟨he,fun h=>hne (sigma_mk_injective h)⟩
end Oberwolfach
