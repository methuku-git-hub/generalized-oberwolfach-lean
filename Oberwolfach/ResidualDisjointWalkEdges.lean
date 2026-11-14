module

public import Oberwolfach.ResidualSimplePathCount

@[expose] public section
/-! Vertex-disjoint walks have disjoint underlying physical edge sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem vertex_disjoint_walk_edge_sets (F:SimpleGraph V) (s:Finset I)
    (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hdisj:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset)):
    (↑s:Set I).PairwiseDisjoint (fun i=>(P i).edges.toFinset) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  induction e using Sym2.ind with
  | _ x y =>
    have hxi : x∈(P i).support.toFinset := by
      apply List.mem_toFinset.mpr
      exact (P i).fst_mem_support_of_mem_edges (List.mem_toFinset.mp hei)
    have hxj : x∈(P j).support.toFinset := by
      apply List.mem_toFinset.mpr
      exact (P j).fst_mem_support_of_mem_edges (List.mem_toFinset.mp hej)
    exact Finset.disjoint_left.mp (hdisj hi hj hij) hxi hxj
end Oberwolfach
