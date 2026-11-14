module

public import Oberwolfach.ResidualSimplePathCount
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section
/-! An exact edge count used before deleting components and path interiors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_edge_count (F:SimpleGraph V) (hF:F.IsRegularOfDegree 2):
    F.edgeFinset.card=Fintype.card V := by
  have h:=F.sum_degrees_eq_twice_card_edges
  have hs : (∑ v, F.degree v) = 2 * Fintype.card V := by
    have hd : ∀ v, F.degree v=2 := fun v=>hF v
    simp [hd, mul_comm]
  omega
end Oberwolfach
