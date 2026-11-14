module

public import Oberwolfach.FactorComponentOrderedCycle

@[expose] public section
/-! Each cycle component has equally many edges and vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem cycle_walk_edge_vertex_count (F:SimpleGraph V) {v:V}
    (p:F.Walk v v) (hp:p.IsCycle):
    p.edges.toFinset.card=p.support.dropLast.toFinset.card := by
  rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
    List.toFinset_card_of_nodup hp.nodup_dropLast_support,
    p.length_edges,List.length_dropLast,p.length_support]
  omega
end Oberwolfach
