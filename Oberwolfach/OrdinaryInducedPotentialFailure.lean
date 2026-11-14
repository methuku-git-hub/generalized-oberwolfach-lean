module

public import Oberwolfach.FiniteSeedFailureMargins

@[expose] public section
/-! The induced-hub concentration error tends to zero uniformly when the
number of physical hubs is at most a fixed multiple of the inner order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach

theorem ordinary_induced_potential_failure_eventually_small
    (K B t ε : ℝ) (d : ℕ) (hK : 0 ≤ K) (hB : 0 < B) (ht : 0 < t) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → (m : ℝ) ≤ K*n →
      (n : ℝ)*m*(2*Real.exp (-2*t^2 /
        ((4*(d:ℝ)+3)^2*((3:ℝ)^4*B/n)*(2*3)*((3:ℝ)^2*B)))) < ε := by
  let D : ℝ := (4*(d:ℝ)+3)^2*((3:ℝ)^4*B)*(2*3)*((3:ℝ)^2*B)
  let c : ℝ := 2*t^2/D
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N₀,hN₀⟩ := eventually_any_polynomial_exponential_failure_below (2*K) c ε 2 hc hε
  refine ⟨max N₀ 1, ?_⟩
  intro n m hn hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hnN : N₀ ≤ n := (le_max_left _ _).trans hn
  have htail := hN₀ n hnN
  have harg : -2*t^2 / ((4*(d:ℝ)+3)^2*((3:ℝ)^4*B/n)*(2*3)*((3:ℝ)^2*B)) = -c*n := by
    dsimp [c,D]
    field_simp [ne_of_gt hn0, ne_of_gt hB, show (4*(d:ℝ)+3) ≠ 0 by positivity]
    <;> ring
  rw [harg]
  have hcoef : (n : ℝ)*m*2 ≤ (2*K)*(n:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hm hn0.le
    nlinarith
  have h := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-c*n)).le
  have heq : (n : ℝ)*m*(2*Real.exp (-c*n)) = ((n:ℝ)*m*2)*Real.exp (-c*n) := by ring
  rw [heq]
  exact h.trans_lt htail
end Oberwolfach
