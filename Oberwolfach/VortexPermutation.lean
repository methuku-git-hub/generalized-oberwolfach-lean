module

public import Oberwolfach.VortexSizeBounds
public import Oberwolfach.ShellPermutation

@[expose] public section

/-! Choosing the permutation together with the fixed vortex geometry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe b c

theorem Vortex.preserving_permutation {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (he : 0 ≤ ε) (heq : ε ≤ 1 / 4) (h : ℕ) (hm : (h : ℝ) ≤ 3 * ε * m / 8) :
    ∃ π : Equiv.Perm V,
      (∀ i, ∀ x, π x ∈ Q.extendedVertices i ↔ x ∈ Q.extendedVertices i) ∧
      (∀ x k, nestedLevel Q.vertices Q.length ((π ^ k) x) =
        nestedLevel Q.vertices Q.length x) ∧
      (∀ x k, 0 < k → k < h → (π ^ k) x ≠ x) := by
  have hs : ∀ i < Q.length, (Q.vertices i \ Q.vertices (i + 1)).Nonempty →
      h ≤ (Q.vertices i \ Q.vertices (i + 1)).card := by
    intro i hi _
    have hh := Q.difference_size_lower he heq (Nat.lt_succ_self i)
      (by omega : i + 1 ≤ Q.length + 1)
    rw [Q.extendedVertices_eq (by omega : i ≤ Q.length),
      Q.extendedVertices_eq (by omega : i + 1 ≤ Q.length)] at hh
    exact_mod_cast hm.trans hh
  have ht : h ≤ (Q.vertices Q.length).card := by
    have hm0 : 0 ≤ ε * (m : ℝ) := mul_nonneg he (Nat.cast_nonneg m)
    have hh : (h : ℝ) ≤ (Q.vertices Q.length).card := by
      have := Q.terminal_lower
      linarith
    exact_mod_cast hh
  obtain ⟨π, hπ, hlevel, hreturn⟩ :=
    nested_shell_permutation Q.vertices Q.length h Q.initial Q.nested hs ht
  refine ⟨π, ?_, hlevel, hreturn⟩
  intro i x
  by_cases hi : i ≤ Q.length
  · rw [Q.extendedVertices_eq hi]
    exact hπ i hi x
  · rw [Q.extendedVertices_empty (by omega)]
    simp

theorem vortex_with_permutation_exists {β ε ρ₀ : ℝ} (hb : 0 < β)
    (he : 0 < ε) (heq : ε < 1 / 4) (hp : 0 < ρ₀) (h : ℕ) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ (V : Type b) [Fintype V] (U : Type c) [Fintype U]
      (G : SimpleGraph V) (D m : ℕ),
      G.IsRegularOfDegree D → (Fintype.card V : ℝ) / 2 ≤ D →
      ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D ≤ 1 →
      m₀ ≤ m → m ≤ Fintype.card V →
      ∃ Q : Vortex U G D β ε m, ∃ π : Equiv.Perm V,
        (∀ i, ∀ x, π x ∈ Q.extendedVertices i ↔ x ∈ Q.extendedVertices i) ∧
        (∀ x k, nestedLevel Q.vertices Q.length ((π ^ k) x) =
          nestedLevel Q.vertices Q.length x) ∧
        (∀ x k, 0 < k → k < h → (π ^ k) x ≠ x) := by
  obtain ⟨N, hN1, hN⟩ := vortex_exists.{b,c} hb he heq hp
  refine ⟨max N ⌈8 * (h : ℝ) / (3 * ε)⌉₊, by omega, ?_⟩
  intro V _ U _ G D m hreg hD hρ hρ1 hm hmn
  obtain ⟨Q⟩ := hN V U G D m hreg hD hρ hρ1 (by omega) hmn
  have hceil : 8 * (h : ℝ) / (3 * ε) ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈8 * (h : ℝ) / (3 * ε)⌉₊ ≤ m by omega))
  have hsize : (h : ℝ) ≤ 3 * ε * m / 8 := by
    have hh := (div_le_iff₀ (show 0 < 3 * ε by positivity)).mp hceil
    nlinarith
  obtain ⟨π, hπ⟩ := Q.preserving_permutation he.le heq.le h hsize
  exact ⟨Q, π, hπ⟩

end Oberwolfach
