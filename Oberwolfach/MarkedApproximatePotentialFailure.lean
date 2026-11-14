module

public import Oberwolfach.OrientationMargins

@[expose] public section
/-! Uniform exponential failure budget for the marked potential event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem marked_approximate_potential_failure_small (d m:ℕ) (B t:ℝ) (hB:0<B) (ht:0<t):
    ∃ N:ℕ,∀ n:ℕ,N≤n→
      8*(n:ℝ)^2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*B/n)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B)))≤1/1000:=by
  let K:ℝ:=(8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*B)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B)
  have hK:0<K:=by dsimp [K];positivity
  let c:ℝ:=2*t^2/K
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (8:ℝ) 2 (c:=c) (p:=1) hc (by norm_num) 1
  refine ⟨max N 1000,?_⟩
  intro n hn
  have hn1000:1000≤n:=le_trans (le_max_right _ _) hn
  have hnpos:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hb:=hN n (le_trans (le_max_left _ _) hn)
  simp only [Real.rpow_one,Real.rpow_two,pow_one] at hb
  have harg:-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*B/n)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B)) = -c*(n:ℝ):=by
    dsimp [c,K]
    field_simp
  rw [harg]
  have hsmall:(1:ℝ)/(n:ℝ)≤1/1000:=by
    apply (div_le_iff₀ hnpos).2
    have :(1000:ℝ)≤n:=by exact_mod_cast hn1000
    linarith
  exact hb.trans hsmall
end Oberwolfach
