module

public import Oberwolfach.OrdinaryInducedParentRegularity
public import Oberwolfach.OrdinaryInducedParentThreshold

@[expose] public section
/-! The deterministic parent density and balance profiles provide the inner
minimum degree, near-regularity, degree-center and conflict inputs together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_inner_parent_conditions_from_profiles
    (P F : SimpleGraph V) (A : Finset V) (Z : Finset U)
    (density α pR pH e δ L : ℝ) (hpR : 0<pR)
    (hthreshold : cycleThreshold 3 + α ≤ density)
    (hmin : ∀ v, density*A.card ≤ ((A ∩ P.neighborFinset v).card : ℝ))
    (hparent : ∀ v, |pR*(P.neighborFinset v ∩ A).card - 2*pH*Z.card| ≤ e)
    (hlo : pR*(A.card:ℝ)/2 ≤ 2*pH*Z.card)
    (hhi : 2*pH*Z.card ≤ 2*pR*A.card)
    (hmargin : e/pR ≤ δ*A.card)
    (hF : ∀ v, (F.degree v : ℝ) ≤ L) :
    let D := 2*pH*Z.card/pR;
    (∀ v : {x : V // x ∈ (A : Set V)},
      (cycleThreshold 3 + α)*A.card ≤ (((P.induce (A : Set V)).degree v) : ℝ)) ∧
    ((A.card:ℝ)/2 ≤ D ∧ D ≤ 2*A.card) ∧
    (∀ v : {x : V // x ∈ (A : Set V)},
      |(((P.induce (A : Set V)).degree v) : ℝ)-D| ≤ δ*A.card) ∧
    (∀ v : {x : V // x ∈ (A : Set V)}, (((F.induce (A : Set V)).degree v) : ℝ) ≤ L) := by
  intro D
  refine ⟨ordinary_induced_parent_threshold_from_density P A density α hthreshold hmin,
    ordinary_induced_parent_degree_center_bounds A Z pR pH hpR hlo hhi, ?_,
    ordinary_induced_conflict_degree_from_ambient F A L hF⟩
  intro v
  exact (ordinary_induced_parent_regularity_from_balance P A Z pR pH e hpR hparent v).trans hmargin
end Oberwolfach
