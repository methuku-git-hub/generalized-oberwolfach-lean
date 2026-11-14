module

public import Oberwolfach.ResidualActualDeletedCounts

@[expose] public section
/-! Every edge incident with the interior of a path in a two-factor belongs
to the path; no edge can be left with a deleted endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_internal_path_edges (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) {u v:V} (p:F.Walk u v) (hp:p.IsPath)
    (x y:V) (hx:x∈p.support.toFinset \ {u,v}) (hxy:F.Adj x y):
    s(x,y)∈p.edges.toFinset := by
  have hx' := Finset.mem_sdiff.mp hx
  have hxu:x≠u := by
    intro h;subst x;exact hx'.2 (by simp)
  have hxv:x≠v := by
    intro h;subst x;exact hx'.2 (by simp)
  obtain ⟨i,hi,hile⟩:=SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hx'.1)
  have hi0:i≠0 := by
    intro h;subst i;apply hxu;simpa using hi.symm
  have hilt:i<p.length := by
    have hh:i≠p.length := by intro h;subst i;apply hxv;simpa using hi.symm
    omega
  have hsub:=p.toSubgraph.neighborSet_subset x
  have hsmall:(p.toSubgraph.neighborSet x).ncard=2 := by
    rw [←hi]
    exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
  have hbig:(F.neighborSet x).ncard=2 := by rw [F.ncard_neighborSet,hF x]
  have hsets:p.toSubgraph.neighborSet x=F.neighborSet x := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [hbig,hsmall]
  apply List.mem_toFinset.mpr
  apply SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp
  apply (SimpleGraph.Subgraph.mem_neighborSet _ _ _).mp
  rw [hsets]
  exact hxy
end Oberwolfach
