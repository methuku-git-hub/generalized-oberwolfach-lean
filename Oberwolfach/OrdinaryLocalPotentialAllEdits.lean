module

public import Oberwolfach.OrdinaryLocalPotentialSymmetricEdits
public import Oberwolfach.OrdinaryLocalPotentialSpokeBound

@[expose] public section
/-! A single quantitative estimate for simultaneous symmetric rim and
spoke-neighborhood edits of a root-omitted local potential. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

theorem ordinary_local_potential_all_edits
    (P Q R F : SimpleGraph V) (T T' : Finset V)
    (hr : 2 ≤ r) (hn : 0 < Fintype.card V)
    (φ : OrdinaryCycle P r → ℝ) (hφ : ∀ C, 0 ≤ φ C)
    (B M L : ℝ) (hB : 0 ≤ B)
    (hφB : ∀ C, φ C ≤ B / (Fintype.card V : ℝ) ^ (r - 1))
    (hQR : ∀ v, ((Q \ R).degree v : ℝ) ≤ M)
    (hRQ : ∀ v, ((R \ Q).degree v : ℝ) ≤ M)
    (hT : (((T \ T') ∪ (T' \ T)).card : ℝ) ≤ L) (v : V) :
    |ordinaryLocalPotential P R F T' φ v - ordinaryLocalPotential P Q F T φ v| ≤
      (r : ℝ)^2 * B * L / Fintype.card V +
      2 * (3 * (r : ℝ)^4 * B * M / Fintype.card V) := by
  have hsp := ordinary_local_potential_spoke_edits_bound P R F T T' hr hn φ hφ B L hB hφB hT v
  have hrim := ordinary_local_potential_symmetric_edits P Q R F T hr hn φ hφ B M hB hφB
    (by intro x; convert hQR x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet])
    (by intro x; convert hRQ x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet]) v
  have htri := abs_sub_le (ordinaryLocalPotential P R F T' φ v)
    (ordinaryLocalPotential P R F T φ v) (ordinaryLocalPotential P Q F T φ v)
  linarith
end Oberwolfach
