module

public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section
/-! The two concentration errors for the sampled pair-profile inputs vanish
uniformly after all constants have been fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_profile_failure_margins (A B t ρ:ℝ)
    (hA:0<A) (hB:0<B) (ht:0<t) (hρ:0<ρ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ M₁ M₂:ℝ,
      0≤M₁→M₁≤2*(n:ℝ)^4→0≤M₂→M₂≤16*(n:ℝ)^4→
      M₁*(2*Real.exp (-2*t^2/(A/n)))+
      M₂*(2*Real.exp (-2*(ρ*n)^2/(B*n)))≤2/(n:ℝ)^2 := by
  obtain ⟨N₁,h₁⟩:=constant_deviation_failure_eventually_small 2 A t hA ht 4 2
  obtain ⟨N₂,h₂⟩:=linear_deviation_failure_eventually_small 16 B ρ hB hρ 4 2
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro n hn M₁ M₂ hM₁ hM₁b hM₂ hM₂b
  have hn0:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hfirst:=h₁ n (by omega) M₁ hM₁ hM₁b
  have hsecond:=h₂ n (by omega) M₂ (B*n) hM₂ hM₂b (mul_pos hB hn0) le_rfl
  calc
    _ ≤ 1/(n:ℝ)^2+1/(n:ℝ)^2 := add_le_add hfirst hsecond
    _ = 2/(n:ℝ)^2 := by ring
end Oberwolfach
