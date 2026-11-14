module

public import Oberwolfach.OrdinaryLocalPotentialAllEdits

@[expose] public section
/-! Transfer a previously established local potential estimate through
simultaneous rim and spoke edits, without resampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

theorem ordinary_local_potential_edited_estimate
    (P Q R F : SimpleGraph V) (T T' : Finset V)
    (hr : 2 ≤ r) (hn : 0 < Fintype.card V)
    (φ : OrdinaryCycle P r → ℝ) (hφ : ∀ C, 0 ≤ φ C)
    (B M L : ℝ) (hB : 0 ≤ B)
    (hφB : ∀ C, φ C ≤ B / (Fintype.card V : ℝ) ^ (r - 1))
    (hQR : ∀ v, ((Q \ R).degree v : ℝ) ≤ M)
    (hRQ : ∀ v, ((R \ Q).degree v : ℝ) ≤ M)
    (hT : (((T \ T') ∪ (T' \ T)).card : ℝ) ≤ L)
    (v : V) (target t : ℝ) (hpot : |ordinaryLocalPotential P Q F T φ v - target| ≤ t) :
    |ordinaryLocalPotential P R F T' φ v - target| ≤
      t + (r : ℝ)^2 * B * L / Fintype.card V +
      2 * (3 * (r : ℝ)^4 * B * M / Fintype.card V) := by
  have he := ordinary_local_potential_all_edits P Q R F T T' hr hn φ hφ B M L hB hφB
    (by intro x; convert hQR x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet])
    (by intro x; convert hRQ x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet]) hT v
  have ht := abs_sub_le (ordinaryLocalPotential P R F T' φ v)
    (ordinaryLocalPotential P Q F T φ v) target
  linarith
end Oberwolfach
