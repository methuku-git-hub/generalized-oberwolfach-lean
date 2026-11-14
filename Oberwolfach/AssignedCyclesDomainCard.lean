module

public import Oberwolfach.GlobalAssignmentReservedFamilies

@[expose] public section
/-! The source vertices occupied by assigned cycles are exactly the union of
their connected components. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem assigned_cycles_union_eq_component_domain
    {V J:Type} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    (F:SimpleGraph V) (cycles:J→F.ConnectedComponent) (root:J→V)
    (C:∀j,F.Walk (root j) (root j))
    (hcomp:∀j,(C j).toSubgraph.verts=(cycles j).supp):
    let Cset:=Finset.univ.biUnion (fun j=>(C j).support.toFinset)
    ∀x,x∈Cset↔∃j,x∈(cycles j).supp:=by
  intro Cset x
  simp only [Cset,Finset.mem_biUnion,Finset.mem_univ,true_and,List.mem_toFinset]
  apply exists_congr
  intro j
  rw [←(C j).mem_verts_toSubgraph,hcomp j]

end Oberwolfach
