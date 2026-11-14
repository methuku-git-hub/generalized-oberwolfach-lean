module

public import Oberwolfach.ActualOldArcHostFromDirectedImages

@[expose] public section
/-! The old-arc containment property used by the residual embedding caller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ActualOldArcContainment
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V)
    (E:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph) (R:V→V→Prop):Prop:=
  ∀(pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop),
    pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)→
    (∀p∈pieces,p.OriginalValid D)→(∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces)→
    (∀x,D x (factorCycleOrientation G E x))→
    ∀x y,s(x,y)∈data.deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))→D x y→R (ψ x) (ψ y)
end Oberwolfach
