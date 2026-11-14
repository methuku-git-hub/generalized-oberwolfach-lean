module

public import Oberwolfach.ResidualTwoEndpointCapacity

@[expose] public section
/-! The exact residual count implies the edge budget for choosing positions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I J:Type} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]

theorem two_factor_residual_position_edge_budget
    (F:SimpleGraph V) (hF:F.IsRegularOfDegree 2)
    (s:Finset I) (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hp:∀i∈s,(P i).IsPath) (hne:∀i∈s,u i≠v i)
    (hP:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (t:Finset J) (root:J→V) (C:∀ j,F.Walk (root j) (root j))
    (hc:∀j∈t,(C j).IsCycle)
    (hC:(↑t:Set J).PairwiseDisjoint (fun j=>(C j).support.toFinset))
    (hcross:∀i∈s,∀j∈t,Disjoint (P i).support.toFinset (C j).support.toFinset)
    (A:Finset V) (hAu:∀i∈s,u i∈A) (hAv:∀i∈s,v i∈A):
    let deletedV := (t.biUnion (fun j=>(C j).support.toFinset)) ∪
      (s.biUnion (fun i=>(P i).support.toFinset \ {u i,v i}))
    let deletedE := (t.biUnion (fun j=>(C j).edges.toFinset)) ∪
      (s.biUnion (fun i=>(P i).edges.toFinset))
    let Q:=F.deleteEdges (deletedE:Set (Sym2 V));
    (Finset.univ\deletedV).card≤Q.edgeFinset.card+A.card ∧
      ∀ x∈deletedV,∀ y,¬Q.Adj x y := by
  have hr:=two_factor_residual_graph_after_disjoint_deletions F hF s u v P hp hne hP t root C hc hC hcross
  have ha:=disjoint_walk_endpoints_card_le F s u v P hne hP A hAu hAv
  dsimp only at hr ⊢
  exact ⟨by omega,hr.2⟩
end Oberwolfach
