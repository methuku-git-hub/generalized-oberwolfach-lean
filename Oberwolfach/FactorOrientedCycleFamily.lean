module

public import Oberwolfach.FactorOrientedComponentCycle

@[expose] public section
/-! Select component cycles in the global orientation, with their actual
component sizes and pairwise disjoint supports. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_component_family_has_forward_cycles
    {X J:Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (E:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (components:J↪G.ConnectedComponent):
    ∃ (root:J→X) (p:∀j,G.Walk (root j) (root j)),
      (∀j,(p j).IsCycle) ∧ (∀j,(p j).length=Fintype.card (components j)) ∧
      (∀j k,k<(p j).length→factorCycleOrientation G E ((p j).getVert k)=(p j).getVert (k+1)) ∧
      (∀j,(p j).toSubgraph.verts=(components j).supp) ∧
      (∀i j,i≠j→Disjoint (p i).support.toFinset (p j).support.toFinset):=by
  choose root p hp hlen hstep hsupp using fun j=>factor_component_has_forward_cycle G hG E (components j)
  refine ⟨root,p,hp,hlen,hstep,hsupp,?_⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hxi':x∈(components i).supp:=by
    rw [←hsupp i]
    exact (p i).mem_verts_toSubgraph.mpr (List.mem_toFinset.mp hxi)
  have hxj':x∈(components j).supp:=by
    rw [←hsupp j]
    exact (p j).mem_verts_toSubgraph.mpr (List.mem_toFinset.mp hxj)
  have hcomp:components i≠components j:=fun h=>hij (components.injective h)
  exact Set.disjoint_left.mp (G.pairwise_disjoint_supp_connectedComponent hcomp) hxi' hxj'
end Oberwolfach
