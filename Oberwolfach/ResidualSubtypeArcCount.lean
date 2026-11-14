module

public import Oberwolfach.ResidualFamilySubtypeFixedOrientation
public import Oberwolfach.PrescribedDependentPositions
public import Oberwolfach.PrescribedArcCount

@[expose] public section
/-! Translate the residual edge-count inequality into the exact directed-arc
inequality used when choosing prescribed positions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem residual_subtype_arc_count (R:Finset V)
    (qs:List (PrescribedSourcePiece {x // x∈R}))
    (hshape:∀p∈qs,p.Shape)
    (hpair:qs.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)):
    (prescribedArcFinset (prescribedDependentDigraph (fun _ : Unit=>qs) ())).card=
      (prescribedDependentGraph (fun _ : Unit=>qs) ()).edgeFinset.card := by
  let pieces:Unit→List (PrescribedSourcePiece {x // x∈R}):=fun _=>qs
  let ps:=prescribedTaggedPieces pieces ()
  have hh:=prescribed_arc_count_eq_edge_count (prescribedSourceGraph ps ()) (prescribedSourceDigraph ps ())
    (prescribed_source_model_representation ps ())
    (prescribed_source_model_arc_graph ps (prescribed_tagged_shape pieces () hshape) ())
    (prescribed_source_model_oriented ps (prescribed_tagged_shape pieces () hshape)
      (prescribed_tagged_apart pieces () hpair) ())
  dsimp only [ps] at hh
  rw [prescribed_tagged_graph,prescribed_tagged_digraph] at hh
  exact hh
end Oberwolfach
