module

public import Oberwolfach.SecondOrderInverse

@[expose] public section

/-! Error bounds when an approximate identity has a potentially large
first-order term whose square is small on the preserved subspace. -/
set_option autoImplicit false
namespace Oberwolfach

theorem second_order_perturbation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Submodule ℝ X) (T K : X →ₗ[ℝ] X)
    (a b c : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hT : ∀ z,z∈S → T z∈S)
    (hL : ∀ z,z∈S → ‖T z-z-K z‖≤a*‖z‖)
    (hK : ∀ z,‖K z‖≤b*‖z‖)
    (hK2 : ∀ z,z∈S → ‖K (K z)‖≤c*‖z‖) (z : X) (hz : z∈S) :
    ‖z-T z‖≤(a+b)*‖z‖ ∧
      ‖(z-T z)-T (z-T z)‖≤(c+b*a+a*(a+b))*‖z‖ := by
  let R (x : X) := T x-x-K x
  have hE (x : X) (hx : x∈S) : ‖x-T x‖≤(a+b)*‖x‖ := by
    have he : x-T x=-(K x+R x) := by dsimp [R];abel
    rw [he,norm_neg]
    calc
      _ ≤ ‖K x‖+‖R x‖ := norm_add_le _ _
      _ ≤ b*‖x‖+a*‖x‖ := add_le_add (hK x) (hL x hx)
      _ = _ := by ring
  refine ⟨hE z hz,?_⟩
  have hzE : z-T z∈S := S.sub_mem hz (hT z hz)
  have he2 : (z-T z)-T (z-T z)=K (K z)+K (R z)-R (z-T z) := by
    dsimp [R]
    simp only [map_sub]
    abel
  rw [he2]
  calc
    _ ≤ ‖K (K z)+K (R z)‖+‖R (z-T z)‖ := norm_sub_le _ _
    _ ≤ (‖K (K z)‖+‖K (R z)‖)+‖R (z-T z)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (c*‖z‖+b*‖R z‖)+a*‖z-T z‖ := add_le_add (add_le_add (hK2 z hz) (hK (R z))) (hL _ hzE)
    _ ≤ (c*‖z‖+b*(a*‖z‖))+a*((a+b)*‖z‖) := by
      gcongr
      · exact hL z hz
      · exact hE z hz
    _ = _ := by ring

end Oberwolfach
