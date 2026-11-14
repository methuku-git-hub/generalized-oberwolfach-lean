module

public import Oberwolfach.PrescribedSourcePieces
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section
/-! A component of an actual two-factor is a cycle, with no separate
assumption that its component has been presented as an ordered list. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

theorem two_factor_is_cycles (F : SimpleGraph V) (hF : F.IsRegularOfDegree 2) :
    F.IsCycles := by
  intro v _
  rw [F.ncard_neighborSet, hF v]

theorem two_factor_component_cycle (F : SimpleGraph V) (hF : F.IsRegularOfDegree 2)
    (v : V) :
    ∃ p : F.Walk v v, p.IsCycle ∧
      p.toSubgraph.verts = (F.connectedComponentMk v).supp := by
  have hne : (F.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [F.ncard_neighborSet, hF v]
    decide
  apply (two_factor_is_cycles F hF).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
  · simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
  · exact hne
end Oberwolfach
