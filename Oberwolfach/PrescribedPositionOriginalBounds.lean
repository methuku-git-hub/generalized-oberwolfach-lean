module

public import Oberwolfach.PrescribedPositionGreedySelection

@[expose] public section
/-! The numerical hypotheses of the prescribed-position lemma supply the
edge and vertex budgets of the greedy selection. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_position_original_budgets (Q:SimpleGraph X) (hdeg:∀x,Q.degree x≤2)
    (A:Finset X) (m z:ℕ) (hedges:Fintype.card X≤Q.edgeFinset.card+A.card)
    (hsize:8*A.card+8*m+4*z+10≤Fintype.card X):
    2*(prescribedClosedNeighbourhoods Q A).card+8*m≤Q.edgeFinset.card ∧
    (prescribedClosedNeighbourhoods Q A).card+4*m+3*z≤Fintype.card X := by
  have hA:=prescribed_closed_neighbourhoods_card Q hdeg A
  constructor <;> omega
end Oberwolfach
