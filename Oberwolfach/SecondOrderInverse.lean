module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

@[expose] public section

/-! A finite-dimensional replacement for the Neumann-series step. A bound
on the square of the error gives surjectivity and a quantitative preimage. -/
set_option autoImplicit false
open scoped BigOperators
namespace Oberwolfach

theorem second_order_inverse {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (T : X →ₗ[ℝ] X) (C q : ℝ) (hq : q<1)
    (hE : ∀ x,‖x-T x‖≤C*‖x‖)
    (hE2 : ∀ x,‖(x-T x)-T (x-T x)‖≤q*‖x‖) (z : X) :
    ∃ w,T w=z ∧ ‖w‖≤(1+C)/(1-q)*‖z‖ := by
  have hinj : Function.Injective T := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hb := hE2 x
    simp only [hx,sub_zero] at hb
    have hn : ‖x‖=0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hn
  obtain ⟨w,hw⟩ := LinearMap.surjective_of_injective hinj z
  refine ⟨w,hw,?_⟩
  have he : w=z+(z-T z)+((w-T w)-T (w-T w)) := by
    rw [map_sub,hw]
    abel
  have hnorm : ‖w‖≤(1+C)*‖z‖+q*‖w‖ := by
    calc
      ‖w‖=‖z+(z-T z)+((w-T w)-T (w-T w))‖ := congrArg norm he
      _ ≤ ‖z+(z-T z)‖+‖(w-T w)-T (w-T w)‖ := norm_add_le _ _
      _ ≤ (‖z‖+‖z-T z‖)+q*‖w‖ := add_le_add (norm_add_le _ _) (hE2 w)
      _ ≤ (‖z‖+C*‖z‖)+q*‖w‖ := by gcongr;exact hE z
      _ = _ := by ring
  have hd : 0<1-q := sub_pos.mpr hq
  calc
    ‖w‖ ≤ ((1+C)*‖z‖)/(1-q) := (le_div_iff₀ hd).mpr (by nlinarith)
    _ = _ := by ring

end Oberwolfach
