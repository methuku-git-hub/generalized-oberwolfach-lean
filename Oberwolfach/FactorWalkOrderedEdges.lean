module

public import Oberwolfach.FactorComponentOrderedCycle

@[expose] public section
/-! The edges of a walk are precisely the consecutive edges of its support. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem walk_edges_eq_ordered_path_edges (F:SimpleGraph V) {u v:V}
    (p:F.Walk u v):p.edges.toFinset = prescribedOrderedPathEdges p.support := by
  induction p with
  | nil => simp [prescribedOrderedPathEdges, SimpleGraph.Walk.edges, SimpleGraph.Walk.darts]
  | @cons u w v h q ih =>
    rw [SimpleGraph.Walk.edges_cons, List.toFinset_cons, SimpleGraph.Walk.support_cons]
    have hsupport := q.cons_tail_support
    rw [←hsupport] at ih ⊢
    simpa [prescribedOrderedPathEdges] using congrArg (fun S : Finset (Sym2 V) => insert s(u,w) S) ih
end Oberwolfach
