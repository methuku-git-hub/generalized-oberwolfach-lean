module

public import Oberwolfach.ActualOldArcContainment
public import Oberwolfach.ActualReindexedFinalEdgeUnion
public import Oberwolfach.ActualSourceOrientationProperties
public import Oberwolfach.PhysicalPackingSym2Family

@[expose] public section
/-! The actual old directed edge containment gives physical coverage of the
symmetric old-edge family used in residual degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_symmetric_edges_physically_covered
    {X V K J I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [DecidableEq K] [DecidableEq J] [Fintype I]
    (G:SimpleGraph X) (data:ActualResidualData (K:=K) (J:=J) G)
    (E:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D) (hEdges:sourcePieceEdgesUnion pieces=G.edgeFinset)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces)
    (halign:∀x,D x (factorCycleOrientation G E x))
    (ψ:X→V) (Pack:Finset (Finset V))
    (hold:ActualOldArcContainment data ψ E (fun x y=>({x,y}:Finset V)∈Pack))
    (b:I≃{i // i∈data.s₁}) (ext:∀i:I,Fin (data.c*data.d+5)↪X)
    (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hsupp:∀i,(data.P (b i).val).support=List.ofFn (ext i))
    (p:∀i:I,G.Walk (inner i 0) (inner i (Fin.last (data.c*data.d))))
    (hp:∀i,(p i).support=List.ofFn (inner i)):
    ∀e∈(data.deletedEdges\(Finset.univ.biUnion (fun i:I=>(p i).edges.toFinset))).image (Sym2.map ψ),
      e.toFinset∈Pack:=by
  have horient:∀x y,G.Adj x y→D x y ∨ D y x:=
    (actual_source_orientation_covers_and_has_unique_incoming G pieces D hpair hvalid hEdges hArcs).1
  apply physical_cover_gives_symmetric_old_edge_cover data _ ψ D horient Pack
  intro x y hxy hd
  have heq:=actual_reindexed_final_edge_union data b ext inner hinner hsupp p hp
  rw [heq] at hxy
  exact hold pieces D hpair hvalid hArcs halign x y hxy hd
end Oberwolfach
