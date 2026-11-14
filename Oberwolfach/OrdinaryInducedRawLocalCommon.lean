module

public import Oberwolfach.OrdinaryInducedRawLocalTail

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

theorem ordinary_induced_raw_local_common
    (P F : SimpleGraph V) (A : Set V)
    (π : Equiv.Perm V) (d r : ℕ) (j : Color)
    (hr : 2 ≤ r) (hn : 0 < Fintype.card A)
    (φ : OrdinaryCycle (P.induce A) r → ℝ) (B : ℝ) (hB : 0 < B)
    (hφ : ∀ C, 0 ≤ φ C ∧ φ C ≤ B / (Fintype.card A : ℝ) ^ (r-1))
    (μ : ∀ e : RawWheelCoordinate V U, FiniteLaw (RawWheelCoordinateState Γ Color e))
    (t : ℝ) (ht : 0 < t) :
    1 - (Fintype.card A : ℝ) * Fintype.card U *
      (2 * Real.exp (-2*t^2 / ((4*(d:ℝ)+3)^2 * ((r:ℝ)^4*B/Fintype.card A) *
        (2*r) * ((r:ℝ)^2*B)))) ≤
    (FiniteLaw.pi μ).probability (fun σ => ∀ (v : A) (u : U),
      |ordinaryLocalPotential (P.induce A) ((rawWheelGraph P σ).induce A) (F.induce A)
        (Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u)) φ v -
        (FiniteLaw.pi μ).expectation (fun τ =>
          ordinaryLocalPotential (P.induce A) ((rawWheelGraph P τ).induce A) (F.induce A)
            (Finset.univ.filter (fun x : A => rawWheelSpokes π d τ j x.val u)) φ v)| < t) := by
  let K : ℝ := 2 * Real.exp (-2*t^2 / ((4*(d:ℝ)+3)^2 *
    ((r:ℝ)^4*B/Fintype.card A) * (2*r) * ((r:ℝ)^2*B)))
  let bad : (A × U) → RawWheelOutcome V U Γ Color → Prop := fun a σ =>
    t ≤ |ordinaryLocalPotential (P.induce A) ((rawWheelGraph P σ).induce A) (F.induce A)
      (Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val a.2)) φ a.1 -
      (FiniteLaw.pi μ).expectation (fun τ =>
        ordinaryLocalPotential (P.induce A) ((rawWheelGraph P τ).induce A) (F.induce A)
          (Finset.univ.filter (fun x : A => rawWheelSpokes π d τ j x.val a.2)) φ a.1)|
  have hbad (a : A × U) : (FiniteLaw.pi μ).probability (bad a) ≤ K :=
    ordinary_induced_raw_local_tail P F A a.2 π d r j hr hn φ B hB hφ μ a.1 t ht
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) (Finset.univ : Finset (A × U))
    bad (fun _ => K) (by intro a _; exact hbad a)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Nat.cast_mul,
    nsmul_eq_mul, Finset.mem_univ, true_implies, not_le, K, bad, Prod.forall] using hh
end Oberwolfach
