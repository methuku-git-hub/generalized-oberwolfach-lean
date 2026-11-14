module

public import Oberwolfach.PrescribedDependentPositions

@[expose] public section
/-! Any vertices omitted from an ordered list of paths and cycles are
isolated. Appending singleton paths makes the source vertex set exact
without changing a single arc or physical edge. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

def prescribedMissingVertices (pieces:∀i,List (PrescribedSourcePiece (X i))) (i:I):Finset (X i):=
  Finset.univ.filter (fun x=>¬∃ p∈pieces i,x∈p.vertices)

def prescribedPadSingletons (pieces:∀i,List (PrescribedSourcePiece (X i))) (i:I):List (PrescribedSourcePiece (X i)):=
  pieces i++(prescribedMissingVertices pieces i).toList.map (fun x=>PrescribedSourcePiece.path [x])

theorem prescribed_padding_shape (pieces:∀i,List (PrescribedSourcePiece (X i)))
    (hshape:∀ i p,p∈pieces i→p.Shape):
    ∀ i p,p∈prescribedPadSingletons pieces i→p.Shape := by
  intro i p hp
  rcases List.mem_append.mp hp with hp|hp
  · exact hshape i p hp
  · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hp
    simp [PrescribedSourcePiece.Shape]

theorem prescribed_padding_apart (pieces:∀i,List (PrescribedSourcePiece (X i)))
    (hapart:∀ i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)):
    ∀ i,(prescribedPadSingletons pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) := by
  intro i
  unfold prescribedPadSingletons
  apply List.pairwise_append.mpr
  refine ⟨hapart i,?_,?_⟩
  · rw [List.pairwise_map]
    apply (Finset.nodup_toList (prescribedMissingVertices pieces i)).imp
    intro x y hne
    simp [PrescribedSourcePiece.vertices,hne]
  · intro p hp q hq
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hq
    have hx':x∈prescribedMissingVertices pieces i:=by simpa using hx
    have hmissing:¬∃ q∈pieces i,x∈q.vertices:=(Finset.mem_filter.mp hx').2
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    have hyx:y=x:=by simpa [PrescribedSourcePiece.vertices] using hy'
    subst y
    exact hmissing ⟨p,hp,List.mem_toFinset.mp hy⟩

theorem prescribed_padding_vertices (pieces:∀i,List (PrescribedSourcePiece (X i))) (i:I):
    prescribedDependentVertices (prescribedPadSingletons pieces) i=Finset.univ := by
  ext x
  simp only [Finset.mem_univ,iff_true,prescribedDependentVertices,Finset.mem_filter,true_and]
  by_cases hx:∃ p∈pieces i,x∈p.vertices
  · obtain ⟨p,hp,hx⟩:=hx
    exact ⟨p,List.mem_append_left _ hp,hx⟩
  · have hm:x∈prescribedMissingVertices pieces i:=Finset.mem_filter.mpr ⟨Finset.mem_univ x,hx⟩
    refine ⟨PrescribedSourcePiece.path [x],List.mem_append_right _ ?_,?_⟩
    · exact List.mem_map.mpr ⟨x,by simpa using hm,rfl⟩
    · simp [PrescribedSourcePiece.vertices]

theorem prescribed_padding_digraph (pieces:∀i,List (PrescribedSourcePiece (X i))) (i:I):
    prescribedDependentDigraph (prescribedPadSingletons pieces) i=prescribedDependentDigraph pieces i := by
  funext x y
  apply propext
  constructor
  · rintro ⟨p,hp,he⟩
    rcases List.mem_append.mp hp with hp|hp
    · exact ⟨p,hp,he⟩
    · obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hp
      simp [PrescribedSourcePiece.arcs,prescribedDirectedPathEdges] at he
  · rintro ⟨p,hp,he⟩
    exact ⟨p,List.mem_append_left _ hp,he⟩

theorem prescribed_padding_graph (pieces:∀i,List (PrescribedSourcePiece (X i))) (i:I):
    prescribedDependentGraph (prescribedPadSingletons pieces) i=prescribedDependentGraph pieces i := by
  unfold prescribedDependentGraph
  congr 1
  ext e
  change (∃p∈prescribedPadSingletons pieces i,e∈p.edges) ↔ ∃p∈pieces i,e∈p.edges
  constructor
  · rintro ⟨p,hp,he⟩
    rcases List.mem_append.mp hp with hp|hp
    · exact ⟨p,hp,he⟩
    · obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hp
      simp [PrescribedSourcePiece.edges,prescribedOrderedPathEdges] at he
  · rintro ⟨p,hp,he⟩
    exact ⟨p,List.mem_append_left _ hp,he⟩
end Oberwolfach
