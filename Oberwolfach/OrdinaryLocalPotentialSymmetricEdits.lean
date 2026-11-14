module

public import Oberwolfach.OrdinaryLocalDeletion

@[expose] public section

/-! Local cycle potentials are stable under both additions and deletions.
The two edited hosts are compared through their common subgraph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

theorem ordinary_local_potential_symmetric_edits
    (P Q R F : SimpleGraph V) (T : Finset V)
    (hr : 2 ≤ r) (hn : 0 < Fintype.card V)
    (φ : OrdinaryCycle P r → ℝ) (hφ : ∀ C, 0 ≤ φ C)
    (B L : ℝ) (hB : 0 ≤ B)
    (hφB : ∀ C, φ C ≤ B / (Fintype.card V : ℝ) ^ (r - 1))
    (hQR : ∀ v, ((Q \ R).degree v : ℝ) ≤ L)
    (hRQ : ∀ v, ((R \ Q).degree v : ℝ) ≤ L) (v : V) :
    |ordinaryLocalPotential P R F T φ v - ordinaryLocalPotential P Q F T φ v| ≤
      2 * (3 * (r : ℝ)^4 * B * L / Fintype.card V) := by
  have hQ : Q \ (Q \ R) = Q ⊓ R := by
    ext x y
    simp only [SimpleGraph.sdiff_adj, SimpleGraph.inf_adj]
    tauto
  have hR : R \ (R \ Q) = Q ⊓ R := by
    ext x y
    simp only [SimpleGraph.sdiff_adj, SimpleGraph.inf_adj]
    tauto
  have a := ordinaryLocalPotential_sdiff_bound P Q F (Q \ R) T hr hn φ hφ B L hB hφB (by intro x; convert hQR x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet]) v
  have b := ordinaryLocalPotential_sdiff_bound P R F (R \ Q) T hr hn φ hφ B L hB hφB (by intro x; convert hRQ x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet]) v
  rw [hQ] at a
  rw [hR] at b
  have htri := abs_sub_le (ordinaryLocalPotential P R F T φ v)
    (ordinaryLocalPotential P (Q ⊓ R) F T φ v) (ordinaryLocalPotential P Q F T φ v)
  rw [abs_sub_comm] at b
  linarith
end Oberwolfach
