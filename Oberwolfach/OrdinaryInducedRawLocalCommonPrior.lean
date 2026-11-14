module

public import Oberwolfach.OrdinaryInducedRawLocalCommon
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section

/-! One event controls every induced-domain root and every physical hub,
with the same original sample and the same preselected cycle weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_raw_local_common_with_prior
    (P F : SimpleGraph V) (A : Set V)
    (π : Equiv.Perm V) (d r : ℕ) (j : Color)
    (hr : 2 ≤ r) (hn : 0 < Fintype.card A)
    (φ : OrdinaryCycle (P.induce A) r → ℝ) (B : ℝ) (hB : 0 < B)
    (hφ : ∀ C, 0 ≤ φ C ∧ φ C ≤ B / (Fintype.card A : ℝ) ^ (r-1))
    (μ : ∀ e : RawWheelCoordinate V U, FiniteLaw (RawWheelCoordinateState Γ Color e))
    (t : ℝ) (ht : 0 < t)
    (E : RawWheelOutcome V U Γ Color → Prop) (a : ℝ)
    (hE : 1-a ≤ (FiniteLaw.pi μ).probability E) :
    1 - a - (Fintype.card A : ℝ) * Fintype.card U *
      (2 * Real.exp (-2*t^2 / ((4*(d:ℝ)+3)^2 * ((r:ℝ)^4*B/Fintype.card A) *
        (2*r) * ((r:ℝ)^2*B)))) ≤
    (FiniteLaw.pi μ).probability (fun σ => E σ ∧ ∀ (v : A) (u : U),
      |ordinaryLocalPotential (P.induce A) ((rawWheelGraph P σ).induce A) (F.induce A)
        (Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u)) φ v -
        (FiniteLaw.pi μ).expectation (fun τ =>
          ordinaryLocalPotential (P.induce A) ((rawWheelGraph P τ).induce A) (F.induce A)
            (Finset.univ.filter (fun x : A => rawWheelSpokes π d τ j x.val u)) φ v)| < t) := by
  have hh := ordinary_induced_raw_local_common P F A π d r j hr hn φ B hB hφ μ t ht
  exact finiteLaw_intersection_lower (FiniteLaw.pi μ) E _ a _ hE hh
end Oberwolfach
