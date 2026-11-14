module

public import Oberwolfach.OrdinaryInducedRawResource
public import Oberwolfach.OrdinarySpokePotentialIdentity

@[expose] public section

/-! Concentration around the actual mean of induced-domain local potentials,
using the original full-space primitive coordinates and permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_raw_local_tail
    (P F : SimpleGraph V) (A : Set V) (u : U)
    (π : Equiv.Perm V) (d r : ℕ) (j : Color)
    (hr : 2 ≤ r) (hn : 0 < Fintype.card A)
    (φ : OrdinaryCycle (P.induce A) r → ℝ) (B : ℝ) (hB : 0 < B)
    (hφ : ∀ C, 0 ≤ φ C ∧ φ C ≤ B / (Fintype.card A : ℝ) ^ (r-1))
    (μ : ∀ e : RawWheelCoordinate V U, FiniteLaw (RawWheelCoordinateState Γ Color e))
    (v : A) (t : ℝ) (ht : 0 < t) :
    (FiniteLaw.pi μ).probability (fun σ => t ≤
      |ordinaryLocalPotential (P.induce A) ((rawWheelGraph P σ).induce A) (F.induce A)
        (Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u)) φ v -
        (FiniteLaw.pi μ).expectation (fun τ =>
          ordinaryLocalPotential (P.induce A) ((rawWheelGraph P τ).induce A) (F.induce A)
            (Finset.univ.filter (fun x : A => rawWheelSpokes π d τ j x.val u)) φ v)|) ≤
      2 * Real.exp (-2*t^2 / ((4*(d:ℝ)+3)^2 * ((r:ℝ)^4*B/Fintype.card A) *
        (2*r) * ((r:ℝ)^2*B))) := by
  let W := ordinaryCycleWheelWeight (U:=Unit) (P.induce A) (F.induce A) r φ 1
  let Q := fun σ : RawWheelOutcome V U Γ Color => (rawWheelGraph P σ).induce A
  let H := fun σ : RawWheelOutcome V U Γ Color => fun (x : A) (_ : Unit) =>
    rawWheelSpokes π d σ j x.val u
  let S := ordinaryInducedRawCoordinates A u π d
  have hW : ∀ w, 0 ≤ W w ∧ W w ≤ B / (Fintype.card A : ℝ)^(r-1) := by
    intro w
    simpa only [W, ordinaryCycleWheelWeight, div_one] using hφ w.val.1
  have hU : Fintype.card Unit ≤ Fintype.card A := by simp only [Fintype.card_unit]; omega
  have hstate : ∀ a σ τ, (∀ e ∈ S a, σ e = τ e) →
      ordinaryResourceState (Q σ) (H σ) a = ordinaryResourceState (Q τ) (H τ) a := by
    intro a σ τ h
    exact ordinary_induced_raw_state_supported P A u π d j a σ τ h
  have hread : ∀ a, ((S a).card : ℝ) ≤ 4*(d:ℝ)+3 := by
    intro a
    exact_mod_cast ordinary_induced_raw_coordinates_card A u π d a
  have hreverse : ∀ e, ((Finset.univ.filter (fun a => e ∈ S a)).card : ℝ) ≤ 4*(d:ℝ)+3 := by
    intro e
    exact_mod_cast ordinary_induced_raw_coordinates_reverse_card A u π d e
  have hid (σ : RawWheelOutcome V U Γ Color) :
      ordinaryPotentialLoad W (Sum.inr (v,())) (Q σ) (H σ) =
        ordinaryLocalPotential (P.induce A) ((rawWheelGraph P σ).induce A) (F.induce A)
          (Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u)) φ v := by
    simpa only [W,Q,H,div_one] using
      ordinary_spoke_potential_eq_local (P.induce A) ((rawWheelGraph P σ).induce A)
        (F.induce A) (H σ) φ 1 v ()
  have hh := ordinaryPotentialLoad_supported_tail (P.induce A) (F.induce A)
    (fun _ : A => fun _ : Unit => True) r hr hn hU W B hB.le hW μ Q H S hstate
    (4*(d:ℝ)+3) (by positivity) hB hread hreverse (Sum.inr (v,())) t ht
  simpa only [hid] using hh
end Oberwolfach
