module

public import Oberwolfach.SharedVortexPermutation

@[expose] public section
/-! Choose one vortex size above all supplied lower thresholds before the
ambient order, and retain the common permutation for every class. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe b c d

theorem shared_vortex_ordered_size_exists {β ε ρ₀:ℝ}
    (hb:0<β) (he:0<ε) (heq:ε<1/4) (hp:0<ρ₀) (h mMatch mGeom Nhost:ℕ):
    ∃ m:ℕ,1≤m ∧ mMatch≤m ∧ mGeom≤m ∧
      ∀ (V:Type b) [Fintype V] (A:Type c) [Nonempty A]
        (U:A→Type d) [∀a,Fintype (U a)] (G:SimpleGraph V) (D:ℕ),
      G.IsRegularOfDegree D → (Fintype.card V:ℝ)/2≤D →
      (∀a,ρ₀ ≤ initialIndexDensity (U a) D) →
      (∀a,initialIndexDensity (U a) D≤1) →
      max m Nhost≤Fintype.card V →
      ∃ Q:∀a,Vortex (U a) G D β ε m, ∃π:Equiv.Perm V,
        (∀a i x,π x∈(Q a).extendedVertices i ↔ x∈(Q a).extendedVertices i) ∧
        (∀a b,(Q a).toVertexVortex=(Q b).toVertexVortex) ∧
        (∀x k,0<k→k<h→(π^k) x≠x) := by
  obtain ⟨m₀,hm₀,hv⟩:=shared_vortex_with_permutation_exists.{b,c,d} hb he heq hp h
  let m:=max m₀ (max mMatch mGeom)
  refine ⟨m,by dsimp [m];omega,by dsimp [m];omega,by dsimp [m];omega,?_⟩
  intro V _ A _ U _ G D hreg hD hlo hhi hn
  exact hv V A U G D m hreg hD hlo hhi (by dsimp [m];omega) (by omega)
end Oberwolfach
