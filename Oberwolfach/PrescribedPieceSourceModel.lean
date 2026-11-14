module

public import Oberwolfach.PrescribedPieceShape
public import Oberwolfach.PrescribedOriginalSourcePieces
public import Oberwolfach.PrescribedPieceArcPhysical

@[expose] public section
/-! Construct the source graph, directed arcs and vertex set directly from
the ordered path-and-cycle pieces. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X:Type} [Fintype X] [DecidableEq I] [DecidableEq X]

def prescribedSourceVertices (ps:List (I×PrescribedSourcePiece X)) (i:I):Finset X:=
  Finset.univ.filter (fun x=>∃ p∈ps,p.1=i ∧ x∈p.2.vertices)

def prescribedSourcePhysical (ps:List (I×PrescribedSourcePiece X)) (i:I):Set (Sym2 X):=
  {e | ∃ p∈ps,p.1=i ∧ e∈p.2.edges}

def prescribedSourceGraph (ps:List (I×PrescribedSourcePiece X)) (i:I):SimpleGraph X:=
  SimpleGraph.fromEdgeSet (prescribedSourcePhysical ps i)

def prescribedSourceDigraph (ps:List (I×PrescribedSourcePiece X)) (i:I) (x y:X):Prop:=
  ∃ p∈ps,p.1=i ∧ (x,y)∈p.2.arcs

theorem prescribed_source_model_vertices (ps:List (I×PrescribedSourcePiece X)) (i:I) (x:X):
    x∈prescribedSourceVertices ps i ↔ ∃ p∈ps,p.1=i ∧ x∈p.2.vertices := by
  simp [prescribedSourceVertices]

theorem prescribed_source_model_edges (ps:List (I×PrescribedSourcePiece X)) (i:I) (e:Sym2 X)
    (he:e∈(prescribedSourceGraph ps i).edgeFinset):
    ∃ p∈ps,p.1=i ∧ e∈p.2.edges := by
  have hh:e∈(prescribedSourceGraph ps i).edgeSet:=SimpleGraph.mem_edgeFinset.mp he
  change e∈(SimpleGraph.fromEdgeSet (prescribedSourcePhysical ps i)).edgeSet at hh
  rw [SimpleGraph.edgeSet_fromEdgeSet] at hh
  exact hh.1

theorem prescribed_source_model_piece_valid (ps:List (I×PrescribedSourcePiece X))
    (hshape:∀ p∈ps,p.2.Shape):∀ p∈ps,p.2.OriginalValid (prescribedSourceDigraph ps p.1) := by
  intro p hp
  cases hpiece:p.2 with
  | path xs =>
    have hn:xs.Nodup:=by simpa [hpiece,PrescribedSourcePiece.Shape] using hshape p hp
    refine ⟨hn,?_⟩
    apply (prescribed_directed_edges_chain (prescribedSourceDigraph ps p.1) xs).mpr
    intro e he
    refine ⟨p,hp,rfl,?_⟩
    simpa [hpiece,PrescribedSourcePiece.arcs] using he
  | cycle a xs =>
    have hh:(a::xs).Nodup ∧ 3≤(a::xs).length:=by simpa [hpiece,PrescribedSourcePiece.Shape] using hshape p hp
    refine ⟨hh.1,hh.2,?_⟩
    apply (prescribed_directed_edges_chain (prescribedSourceDigraph ps p.1) ((a::xs)++[a])).mpr
    intro e he
    refine ⟨p,hp,rfl,?_⟩
    simpa [hpiece,PrescribedSourcePiece.arcs] using he

theorem prescribed_source_model_arc_graph (ps:List (I×PrescribedSourcePiece X))
    (hshape:∀ p∈ps,p.2.Shape):∀ i x y,prescribedSourceDigraph ps i x y→(prescribedSourceGraph ps i).Adj x y := by
  intro i x y hxy
  obtain ⟨p,hp,hpi,he⟩:=hxy
  apply (SimpleGraph.fromEdgeSet_adj _).mpr
  constructor
  · refine ⟨p,hp,hpi,?_⟩
    rw [prescribed_piece_edges_are_arc_images]
    exact Finset.mem_image.mpr ⟨(x,y),he,rfl⟩
  · intro h
    subst y
    exact prescribed_piece_no_loops p.2 (hshape p hp) x he
end Oberwolfach
