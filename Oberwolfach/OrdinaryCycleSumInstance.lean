module

public import Oberwolfach.OrdinaryShiftedRetainedEventRootTargets

@[expose] public section
/-! The finite sum over all ordinary cycles is independent of the choice of
decidable equality used to enumerate the finite graph type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_edge_sum_fin_decidable (n r:ℕ) (P:SimpleGraph (Fin n))
    (w:OrdinaryCycle P r→ℝ) (x y:Fin n):
    (letI:DecidableEq (Fin n):=Classical.decEq _
     ∑C:OrdinaryCycle P r,if C.val.val.Adj x y then w C else 0)=
    (letI:DecidableEq (Fin n):=instDecidableEqFin n
     ∑C:OrdinaryCycle P r,if C.val.val.Adj x y then w C else 0) :=by
  apply Finset.sum_congr
  · ext C; simp
  · intro C hC; rfl
end Oberwolfach
