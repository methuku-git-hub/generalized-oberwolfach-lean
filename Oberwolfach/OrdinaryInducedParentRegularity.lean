module

public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! The existing parent balance profile gives near-regularity of the fixed
inner induced host, with its degree center determined by the same profile. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_parent_regularity_from_balance
    (P : SimpleGraph V) (A : Finset V) (Z : Finset U) (pR pH e : ℝ) (hpR : 0<pR)
    (hparent : ∀ v, |pR * (P.neighborFinset v ∩ A).card - 2*pH*Z.card| ≤ e)
    (v : {x : V // x ∈ (A : Set V)}) :
    |(((P.induce (A : Set V)).degree v) : ℝ) - 2*pH*Z.card/pR| ≤ e/pR := by
  have he := induced_degree_intersection P A v
  have hscale : pR * ((((P.induce (A : Set V)).degree v) : ℝ) - 2*pH*Z.card/pR) =
      pR * (P.neighborFinset v.val ∩ A).card - 2*pH*Z.card := by
    rw [he]
    field_simp [hpR.ne']
  have hh : pR * |(((P.induce (A : Set V)).degree v) : ℝ) - 2*pH*Z.card/pR| ≤ e := by
    calc
      _ = |pR * ((((P.induce (A : Set V)).degree v) : ℝ) - 2*pH*Z.card/pR)| := by
        rw [abs_mul, abs_of_pos hpR]
      _ = |pR * (P.neighborFinset v.val ∩ A).card - 2*pH*Z.card| := by rw [hscale]
      _ ≤ e := hparent v.val
  apply (le_div_iff₀ hpR).2
  nlinarith

theorem ordinary_induced_parent_degree_center_bounds
    (A : Finset V) (Z : Finset U) (pR pH : ℝ) (hpR : 0<pR)
    (hlo : pR*(A.card:ℝ)/2 ≤ 2*pH*Z.card)
    (hhi : 2*pH*Z.card ≤ 2*pR*A.card) :
    (A.card:ℝ)/2 ≤ 2*pH*Z.card/pR ∧ 2*pH*Z.card/pR ≤ 2*A.card := by
  constructor
  · apply (le_div_iff₀ hpR).2
    linarith
  · apply (div_le_iff₀ hpR).2
    linarith
end Oberwolfach
