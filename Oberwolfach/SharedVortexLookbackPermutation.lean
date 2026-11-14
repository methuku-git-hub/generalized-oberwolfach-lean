module

public import Oberwolfach.VortexLookbackExtendFixedVertices
public import Oberwolfach.VortexPermutation

@[expose] public section
/-! Select one physical vertex vortex and one preserving permutation, then
extend it by a nested index sequence for each nonempty class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe b c d

theorem shared_vortex_lookback_with_permutation_exists {β ε ρ₀ : ℝ} (hb : 0 < β)
    (he : 0 < ε) (heq : ε < 1 / 4) (hp : 0 < ρ₀) (t h : ℕ) (ht:1≤t) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ (V : Type b) [Fintype V] (A : Type c) [Nonempty A]
      (U : A → Type d) [∀ a,Fintype (U a)] (G : SimpleGraph V) (D m : ℕ),
      G.IsRegularOfDegree D → (Fintype.card V : ℝ) / 2 ≤ D →
      (∀ a, ρ₀ ≤ initialIndexDensity (U a) D) →
      (∀ a, initialIndexDensity (U a) D ≤ 1) →
      m₀ ≤ m → m ≤ Fintype.card V →
      ∃ Q : ∀ a, VortexLookback (U a) G D β ε m t, ∃ π : Equiv.Perm V,
        (∀ a i x, π x ∈ (Q a).toVortex.extendedVertices i ↔ x ∈ (Q a).toVortex.extendedVertices i) ∧
        (∀ a b, (Q a).toVortex.toVertexVortex = (Q b).toVortex.toVertexVortex) ∧
        (∀ x k, 0 < k → k < h → (π ^ k) x ≠ x) := by
  have he1 : ε < 1 := by linarith
  obtain ⟨N₁,hN₁,hv⟩ := vertexVortex_lookback_exists.{b} (η:=β/2) (by positivity) he he1 t ht
  obtain ⟨N₂,hN₂,hext⟩ := vortex_lookback_extend_fixed_vertices.{b,d} hb he heq hp t ht
  let N := max N₁ (max N₂ ⌈8*(h:ℝ)/(3*ε)⌉₊)
  refine ⟨N,by dsimp [N]; omega,?_⟩
  intro V _ A _ U _ G D m hreg hD hρlo hρhi hm hmn
  have hN1 : N₁ ≤ m := by dsimp [N] at hm;omega
  have hN2 : N₂ ≤ m := by dsimp [N] at hm;omega
  obtain ⟨Qv⟩ := hv V G D m hreg hN1 hmn
  have hex : ∀ a, ∃ Q : VortexLookback (U a) G D β ε m t, Q.toVortex.toVertexVortex=Qv.toVertexVortex := by
    intro a
    exact hext V (U a) G D m hreg hD (hρlo a) (hρhi a) hN2 hmn Qv
  choose Q hQ using hex
  let a₀ : A := Classical.choice ‹Nonempty A›
  have hceil : 8 * (h : ℝ) / (3 * ε) ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈8*(h:ℝ)/(3*ε)⌉₊ ≤ m from by dsimp [N] at hm;omega))
  have hsize : (h : ℝ) ≤ 3 * ε * m / 8 := by
    have hh := (div_le_iff₀ (show 0 < 3 * ε by positivity)).mp hceil
    nlinarith
  obtain ⟨π,hpres,hlevel,hshort⟩ := (Q a₀).toVortex.preserving_permutation he.le heq.le h hsize
  refine ⟨Q,π,?_,?_,hshort⟩
  · intro a i x
    have hlen : (Q a).toVortex.length = (Q a₀).toVortex.length := by
      have ha:=congrArg VertexVortex.length (hQ a)
      have hb':=congrArg VertexVortex.length (hQ a₀)
      exact ha.trans hb'.symm
    have hsets : (Q a).toVortex.vertices = (Q a₀).toVortex.vertices := by
      have ha:=congrArg VertexVortex.vertices (hQ a)
      have hb':=congrArg VertexVortex.vertices (hQ a₀)
      exact ha.trans hb'.symm
    have hs : (Q a).toVortex.extendedVertices i = (Q a₀).toVortex.extendedVertices i := by
      simp only [Vortex.extendedVertices,hlen,hsets]
    simpa only [hs] using hpres i x
  · intro a b
    exact (hQ a).trans (hQ b).symm
end Oberwolfach
