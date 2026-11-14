module

public import Oberwolfach.SparseAlternatingRemainder
public import Oberwolfach.SparseOppositeSquareBound
public import Oberwolfach.SparseOperatorBounds
public import Oberwolfach.SecondOrderPerturbation

@[expose] public section

/-! The error operator preserves the zero-marginal subspace and its
square is a contraction under the explicit intersection-error bound. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem sparse_error_contraction (H : A → B → Prop) (p q : B → ℝ)
    (L δ D : ℝ) (h : SparseIntersectionData H p q L δ D)
    (ha : 0<Fintype.card A) (hb : 0<Fintype.card B)
    (hsmall : δ+D/(Fintype.card A:ℝ)+1/(Fintype.card B:ℝ)≤1/(200*L^6))
    (z : A×B → ℝ) (hz : z∈zeroMarginalSpace H) :
    ‖z-sparseAlternatingMap H q z‖≤9*L^3*‖z‖ ∧
    ‖(z-sparseAlternatingMap H q z)-sparseAlternatingMap H q (z-sparseAlternatingMap H q z)‖≤(1/2:ℝ)*‖z‖ := by
  let ε := δ+D/(Fintype.card A:ℝ)+1/(Fintype.card B:ℝ)
  have hL := h.L_nonneg
  have hδ := h.delta_nonneg
  have hD := h.D_nonneg
  have hε0 : 0≤ε := by dsimp [ε];positivity
  have hL6 : 1≤L^6 := one_le_pow₀ h.one_le_L
  have hL3 : 0≤L^3 := by positivity
  have hden : 0<200*L^6 := by positivity
  have hεbound : ε*(200*L^6)≤1 := (le_div_iff₀ hden).mp hsmall
  have hε1 : ε≤1 := by
    have hh := mul_le_mul_of_nonneg_left hL6 hε0
    nlinarith
  have hh := second_order_perturbation (zeroMarginalSpace H)
    (sparseAlternatingMap H q) (sparseOppositeMap H q) (8*L^3*ε) (L^3) (8*L^6*ε)
    (by positivity) (by positivity)
    (fun z _=>sparseAlternatingMap_zero_marginals H q z)
    (fun z hz=>sparseRemainderMap_norm H p q L δ D h ha hb z hz)
    (fun z=>sparseOppositeMap_norm H q z L hL h.inverse_bounds ha hb)
    (fun z hz=>sparseOppositeMap_square_norm H p q L δ D h ha hb z hz.2.1) z hz
  constructor
  · calc
      _ ≤ (8*L^3*ε+L^3)*‖z‖ := hh.1
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hε1 (show 0≤8*L^3 by positivity)]
  · have hcoeff : 8*L^6*ε+L^3*(8*L^3*ε)+(8*L^3*ε)*(8*L^3*ε+L^3)≤(1/2:ℝ) := by
      have he := mul_le_mul_of_nonneg_left hε1 (show 0≤64*L^6*ε by positivity)
      have h88 : 88*L^6*ε≤(1/2:ℝ) := by nlinarith
      nlinarith
    exact hh.2.trans (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))

end Oberwolfach
