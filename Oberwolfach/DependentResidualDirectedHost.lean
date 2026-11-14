module

public import Oberwolfach.PrescribedDependentPhysical
public import Oberwolfach.PrescribedPieceArcPhysical

@[expose] public section
/-! Every residual source edge has an oriented source arc, so the directed
placement condition implies physical containment in the host. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_dependent_graph_edge_has_arc
    {I:Type} [Fintype I] [DecidableEq I] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]
    (pieces:∀i,List (PrescribedSourcePiece (X i))) (i:I) (x y:X i)
    (hxy:(prescribedDependentGraph pieces i).Adj x y):
    prescribedDependentDigraph pieces i x y ∨ prescribedDependentDigraph pieces i y x:=by
  obtain ⟨⟨p,hp,he⟩,_⟩:=(SimpleGraph.fromEdgeSet_adj _).mp hxy
  rw [prescribed_piece_edges_are_arc_images] at he
  obtain ⟨⟨v,w⟩,hv,heq⟩:=Finset.mem_image.mp he
  change s(v,w)=s(x,y) at heq
  rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inl ⟨p,hp,hv⟩
  · exact Or.inr ⟨p,hp,hv⟩

theorem prescribed_dependent_residual_images_in_host
    {I V:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]
    (pieces:∀i,List (PrescribedSourcePiece (X i))) (Φ:∀i,X i→V)
    (P:SimpleGraph V) (Dstar:V→V→Prop)
    (hstar:∀x y,Dstar x y→P.Adj x y)
    (harc:∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y)):
    ∀i,((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))⊆P.edgeFinset:=by
  intro i target htarget
  obtain ⟨edge,hedge,rfl⟩:=Finset.mem_image.mp htarget
  induction edge using Sym2.ind with
  | _ x y =>
    have hxy:(prescribedDependentGraph pieces i).Adj x y:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hedge
    apply SimpleGraph.mem_edgeFinset.mpr
    change P.Adj (Φ i x) (Φ i y)
    rcases prescribed_dependent_graph_edge_has_arc pieces i x y hxy with h|h
    · exact hstar _ _ (harc i x y h)
    · exact (hstar _ _ (harc i y x h)).symm
end Oberwolfach
