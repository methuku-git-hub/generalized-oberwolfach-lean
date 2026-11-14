module

public import Oberwolfach.OrdinaryLocalLoads

@[expose] public section

/-! Dividing fixed parent coefficients commutes with the rooted local sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

theorem ordinary_local_potential_div
    (P Q F:SimpleGraph V) (T:Finset V) (φ:OrdinaryCycle P r→ℝ) (c:ℝ) (v:V):
    ordinaryLocalPotential P Q F T (fun C=>φ C/c) v=ordinaryLocalPotential P Q F T φ v/c := by
  unfold ordinaryLocalPotential
  rw [Finset.sum_div]
  apply Finset.sum_congr
  · ext C; simp
  · intro C _
    split_ifs <;> simp
end Oberwolfach
