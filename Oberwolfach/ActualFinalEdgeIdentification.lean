module

public import Oberwolfach.ActualBufferedFinalPathIdentification
public import Oberwolfach.FactorWalkOrderedEdges

@[expose] public section
/-! The edge set of the final path in the residual-degree theorem is the
actual final deleted edge set whenever both use the same buffered parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_final_path_edge_set_matches_buffered_sequence
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (i:{i // i∈data.s₁})
    (ext:Fin (data.c*data.d+5)↪X) (inner:Fin (data.c*data.d+1)↪X)
    (hinner:∀p,inner p=ext ⟨p.val+2,by omega⟩)
    (hsupp:(data.P i.val).support=List.ofFn ext)
    {u v:X} (p:F.Walk u v) (hp:p.support=List.ofFn inner):
    p.edges.toFinset=(data.path (.inl i)).edges.toFinset:=by
  have hq:=(actual_final_path_matches_buffered_sequence data i ext inner hinner hsupp).2.2
  rw [walk_edges_eq_ordered_path_edges F p,walk_edges_eq_ordered_path_edges F (data.path (.inl i)),hp,hq]
end Oberwolfach
