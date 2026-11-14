module

public import Oberwolfach.ResidualCycleSupport
public import Oberwolfach.ResidualDisjointWalkEdges

@[expose] public section
/-! Vertex-disjoint cycle components have equally many edges and vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem disjoint_cycle_walks_edge_vertex_count (F:SimpleGraph V) (s:Finset I)
    (root:I→V) (C:∀ i,F.Walk (root i) (root i))
    (hcycle:∀i∈s,(C i).IsCycle)
    (hdisj:(↑s:Set I).PairwiseDisjoint (fun i=>(C i).support.toFinset)):
    (s.biUnion (fun i=>(C i).edges.toFinset)).card =
      (s.biUnion (fun i=>(C i).support.toFinset)).card := by
  have he:=vertex_disjoint_walk_edge_sets F s root root C hdisj
  rw [Finset.card_biUnion he,Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro i hi
  exact cycle_walk_edge_full_vertex_count F (C i) (hcycle i hi)
end Oberwolfach
