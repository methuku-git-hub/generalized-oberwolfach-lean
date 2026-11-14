module

public import Oberwolfach.OrdinaryComplementRemainderDecomposition
public import Oberwolfach.GraphDeletion

@[expose] public section
/-! The embedded complement of whole cycle components has degree two at
its image vertices and degree zero elsewhere. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_piece_degree {n:ℕ}
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2)
    (C:Finset F.ConnectedComponent)
    (fC:{x:Fin n // F.connectedComponentMk x∉C}↪Fin n) (v:Fin n):
    (((F.induce {x | F.connectedComponentMk x∉C}).map fC).degree v)=
      if v∈Set.range fC then 2 else 0 :=by
  have hreg:(F.induce {x | F.connectedComponentMk x∉C}).IsRegularOfDegree 2:=by
    intro x
    have hs:F.neighborSet x.val⊆{x | F.connectedComponentMk x∉C}:=by
      intro y hxy
      change F.connectedComponentMk y∉C
      have heq:F.connectedComponentMk y=F.connectedComponentMk x.val:=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
      have hx:F.connectedComponentMk x.val∉C:=x.property
      simpa only [heq] using hx
    simpa only [hF x.val] using (F.degree_induce_of_neighborSet_subset hs)
  by_cases hv:v∈Set.range fC
  · obtain ⟨x,rfl⟩:=hv
    simp only [Set.mem_range_self,ite_true]
    have hh:=SimpleGraph.degree_map_apply (F.induce {x | F.connectedComponentMk x∉C}) fC x
    rw [hreg x] at hh
    convert hh using 1
  · simp only [hv,ite_false]
    have hiso:(((F.induce {x | F.connectedComponentMk x∉C}).map fC).IsIsolated v):=by
      intro y hxy
      obtain ⟨a,b,hab,ha,hb⟩:=(SimpleGraph.map_adj fC (F.induce {x | F.connectedComponentMk x∉C}) v y).1 hxy
      exact hv ⟨a,ha⟩
    exact hiso.degree_eq_zero
end Oberwolfach
