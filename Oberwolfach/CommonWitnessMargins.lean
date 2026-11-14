module

public import Oberwolfach.CommonWitnessTransfer

@[expose] public section

/-! Choose the deletion tolerance before any graph or random outcome.
The cycle and path coefficients remain positive, while all three errors
fit a prescribed common error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem commonWitness_error_margins (r : ℕ) (K bc bp η : ℝ)
    (hK : 0≤K) (hbc : 0<bc) (hbp : 0<bp) (hη : 0<η) :
    ∃ ζ : ℝ,0<ζ ∧ η/4+2*ζ≤η ∧ 4*ζ≤η ∧ η/4+η/4+K*ζ≤η ∧
      bc/2≤bc-2*(r+5:ℕ)*ζ ∧ bp/2≤bp-2*(r+4:ℕ)*ζ := by
  let ζ := min (η/8) (min (η/(4*(K+1))) (min (bc/(4*(r+5:ℕ))) (bp/(4*(r+4:ℕ)))))
  have hζ : 0<ζ := by dsimp [ζ];positivity
  have hz1 : ζ≤η/8 := min_le_left _ _
  have hz2 : ζ≤η/(4*(K+1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hz3 : ζ≤bc/(4*(r+5:ℕ)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hz4 : ζ≤bp/(4*(r+4:ℕ)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh2 := (le_div_iff₀ (by positivity : (0:ℝ)<4*(K+1))).mp hz2
  have hh3 := (le_div_iff₀ (by positivity : (0:ℝ)<4*(r+5:ℕ))).mp hz3
  have hh4 := (le_div_iff₀ (by positivity : (0:ℝ)<4*(r+4:ℕ))).mp hz4
  exact ⟨ζ,hζ,by linarith,by linarith,by nlinarith,by nlinarith,by nlinarith⟩

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem commonWitnessEstimates_mono
    (P : SimpleGraph V) (π : Equiv.Perm V) (d r : ℕ) (D p k s₀ : ℝ)
    {es eo el bc bp es' eo' el' bc' bp' : ℝ}
    (weight : (Fin (r+4+1)→V)→ℝ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) (κ : V→Bool) (u u' : U)
    (hs : es≤es') (ho : eo≤eo') (hl : el≤el') (hc : bc'≤bc) (hp : bp'≤bp)
    (h : CommonWitnessEstimates P π d r D p k s₀ es eo el bc bp weight σ H κ u u') :
    CommonWitnessEstimates P π d r D p k s₀ es' eo' el' bc' bp' weight σ H κ u u' := by
  refine ⟨fun b=>(h.1 b).trans (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)),
    h.2.1.trans (mul_le_mul_of_nonneg_right ho (Nat.cast_nonneg _)),?_,?_,?_⟩
  · exact fun b v=>(h.2.2.1 b v).trans hl
  · exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans h.2.2.2.1
  · exact fun v v' hv b=>(mul_le_mul_of_nonneg_right hp (by positivity)).trans (h.2.2.2.2 v v' hv b)

end Oberwolfach
