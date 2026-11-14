module

public import Oberwolfach.OrdinaryInducedRawLocalCommon
public import Oberwolfach.OrdinaryLocalPotentialEditedEstimate

@[expose] public section
/-! One original sample controls all later bounded rim and spoke edits of
all fixed inner-domain root potentials, around their unedited means. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_raw_edited_common
    (P F : SimpleGraph V) (A : Set V)
    (π : Equiv.Perm V) (d r : ℕ) (j : Color)
    (hr : 2 ≤ r) (hn : 0 < Fintype.card A)
    (φ : OrdinaryCycle (P.induce A) r → ℝ) (B : ℝ) (hB : 0 < B)
    (hφ : ∀ C, 0 ≤ φ C ∧ φ C ≤ B / (Fintype.card A : ℝ) ^ (r-1))
    (μ : ∀ e : RawWheelCoordinate V U, FiniteLaw (RawWheelCoordinateState Γ Color e))
    (t M L : ℝ) (ht : 0 < t) :
    1 - (Fintype.card A : ℝ) * Fintype.card U *
      (2 * Real.exp (-2*t^2 / ((4*(d:ℝ)+3)^2 * ((r:ℝ)^4*B/Fintype.card A) *
        (2*r) * ((r:ℝ)^2*B)))) ≤
    (FiniteLaw.pi μ).probability (fun σ => ∀ (v : A) (u : U)
        (Q' : SimpleGraph A) (T' : Finset A),
      (∀ x, ((((rawWheelGraph P σ).induce A) \ Q').degree x : ℝ) ≤ M) →
      (∀ x, ((Q' \ ((rawWheelGraph P σ).induce A)).degree x : ℝ) ≤ M) →
      (((((Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u)) \ T') ∪
        (T' \ (Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u)))).card : ℝ) ≤ L) →
      |ordinaryLocalPotential (P.induce A) Q' (F.induce A) T' φ v -
        (FiniteLaw.pi μ).expectation (fun τ =>
          ordinaryLocalPotential (P.induce A) ((rawWheelGraph P τ).induce A) (F.induce A)
            (Finset.univ.filter (fun x : A => rawWheelSpokes π d τ j x.val u)) φ v)| ≤
        t + (r : ℝ)^2 * B * L / Fintype.card A +
          2 * (3 * (r : ℝ)^4 * B * M / Fintype.card A)) := by
  apply (ordinary_induced_raw_local_common P F A π d r j hr hn φ B hB hφ μ t ht).trans
  apply finiteLaw_probability_mono
  intro σ hgood v u Q' T' hQR hRQ hT
  apply ordinary_local_potential_edited_estimate (P.induce A) ((rawWheelGraph P σ).induce A)
    Q' (F.induce A) (Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u)) T'
    hr hn φ (fun C => (hφ C).1) B M L hB.le (fun C => (hφ C).2)
    (by intro x; convert hQR x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet])
    (by intro x; convert hRQ x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet]) hT v
  exact le_of_lt (hgood v u)
end Oberwolfach
