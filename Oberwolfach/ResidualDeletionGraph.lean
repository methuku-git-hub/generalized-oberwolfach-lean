module

public import Oberwolfach.ResidualDeletedVertexIncident
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section
/-! The residual edge and vertex formulas define a consistent graph with the
claimed edge count; the removed vertices are isolated in the ambient graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I J:Type} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]

theorem two_factor_residual_graph_after_disjoint_deletions
    (F:SimpleGraph V) (hF:F.IsRegularOfDegree 2)
    (s:Finset I) (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hp:∀i∈s,(P i).IsPath) (hne:∀i∈s,u i≠v i)
    (hP:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (t:Finset J) (root:J→V) (C:∀ j,F.Walk (root j) (root j))
    (hc:∀j∈t,(C j).IsCycle)
    (hC:(↑t:Set J).PairwiseDisjoint (fun j=>(C j).support.toFinset))
    (hcross:∀i∈s,∀j∈t,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let deletedV := (t.biUnion (fun j=>(C j).support.toFinset)) ∪
      (s.biUnion (fun i=>(P i).support.toFinset \ {u i,v i}))
    let deletedE := (t.biUnion (fun j=>(C j).edges.toFinset)) ∪
      (s.biUnion (fun i=>(P i).edges.toFinset))
    let Q:=F.deleteEdges (deletedE:Set (Sym2 V));
    Q.edgeFinset.card+s.card=(Finset.univ\deletedV).card ∧
      ∀ x∈deletedV,∀ y,¬Q.Adj x y := by
  dsimp only
  constructor
  · rw [SimpleGraph.edgeFinset_deleteEdges]
    exact two_factor_residual_count_after_disjoint_deletions F hF s u v P hp hne hP t root C hc hC hcross
  · intro x hx y hxy
    have hh:=SimpleGraph.deleteEdges_adj.mp hxy
    exact hh.2 (two_factor_deleted_vertex_incident F hF s u v P hp t root C hc x y hh.1 hx)
end Oberwolfach
