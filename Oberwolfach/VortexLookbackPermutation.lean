module

public import Oberwolfach.VortexLookback
public import Oberwolfach.VortexPermutation

@[expose] public section
/-! Select the strengthened vortex together with a preserving permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe b c

theorem vortex_lookback_with_permutation_exists {β ε ρ₀ : ℝ} (hb : 0 < β)
    (he : 0 < ε) (heq : ε < 1 / 4) (hp : 0 < ρ₀) (t h : ℕ) (ht:1≤t) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ (V : Type b) [Fintype V] (U : Type c) [Fintype U]
      (G : SimpleGraph V) (D m : ℕ),
      G.IsRegularOfDegree D → (Fintype.card V : ℝ) / 2 ≤ D →
      ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D ≤ 1 →
      m₀ ≤ m → m ≤ Fintype.card V →
      ∃ Q : VortexLookback U G D β ε m t, ∃ π : Equiv.Perm V,
        (∀ i x, π x ∈ Q.toVortex.extendedVertices i ↔ x ∈ Q.toVortex.extendedVertices i) ∧
        (∀ x k, 0 < k → k < h → (π ^ k) x ≠ x) := by
  obtain ⟨N₁,hN₁,hv⟩ := vortex_lookback_exists.{b,c} hb he heq hp t ht
  let N := max N₁ ⌈8*(h:ℝ)/(3*ε)⌉₊
  refine ⟨N,by dsimp [N]; omega,?_⟩
  intro V _ U _ G D m hreg hD hρlo hρhi hm hmn
  obtain ⟨Q⟩ := hv V U G D m hreg hD hρlo hρhi (by dsimp [N] at hm;omega) hmn
  have hceil : 8 * (h : ℝ) / (3 * ε) ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈8*(h:ℝ)/(3*ε)⌉₊ ≤ m from by dsimp [N] at hm;omega))
  have hsize : (h : ℝ) ≤ 3 * ε * m / 8 := by
    have hh := (div_le_iff₀ (show 0 < 3 * ε by positivity)).mp hceil
    nlinarith
  obtain ⟨π,hpres,hlevel,hshort⟩ := Q.toVortex.preserving_permutation he.le heq.le h hsize
  exact ⟨Q,π,hpres,hshort⟩
end Oberwolfach
