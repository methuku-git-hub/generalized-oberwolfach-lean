module

public import Oberwolfach.Vortex
public import Oberwolfach.VertexVortexLookback

@[expose] public section
/-! A paired vortex with stronger fixed-depth parent estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe b c

structure VortexLookback {V:Type b} [Fintype V] (U:Type c) [Fintype U]
    (G:SimpleGraph V) (D:ℕ) (β ε:ℝ) (m t:ℕ) extends Vortex U G D β ε m where
  centre_estimates_lookback:∀i≤length,0 < i →
    |2*((indices i).card:ℝ)/initialIndexDensity U D-((D:ℝ)/Fintype.card V)*(vertices i).card|≤β*(vertices i).card ∧
    ∀x∈vertices (i-(t+1)),
      |((G.neighborFinset x∩vertices i).card:ℝ)-2*(indices i).card/initialIndexDensity U D|≤β*(vertices i).card

theorem vortex_lookback_exists {β ε ρ₀ : ℝ} (hb : 0 < β) (he : 0 < ε)
    (heq : ε < 1 / 4) (hp : 0 < ρ₀) (t:ℕ) (ht:1≤t) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ (V : Type b) [Fintype V] (U : Type c) [Fintype U]
      (G : SimpleGraph V) (D m : ℕ),
      G.IsRegularOfDegree D → (Fintype.card V : ℝ) / 2 ≤ D →
      ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D ≤ 1 →
      m₀ ≤ m → m ≤ Fintype.card V → Nonempty (VortexLookback U G D β ε m t) := by
  have he1 : ε < 1 := by linarith
  obtain ⟨N₁, hN₁1, hN₁⟩ := vertexVortex_lookback_exists.{b} (η := β / 2) (by positivity) he he1 t ht
  obtain ⟨N₂, hN₂1, hN₂⟩ := eventually_vortex_error_budget hb he he1 hp
  refine ⟨max N₁ N₂, by omega, ?_⟩
  intro V _ U _ G D m hreg hDmin hρmin hρmax hm hmn
  have hmpos : 0 < m := by omega
  have hnpos : 0 < Fintype.card V := by omega
  have hnreal : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
  have hDpos : (0 : ℝ) < D := by linarith
  let ρ := initialIndexDensity U D
  have hρpos : 0 < ρ := hp.trans_le hρmin
  have hcentre : 2 * (Fintype.card U : ℝ) = ρ * D := by
    dsimp only [ρ, initialIndexDensity]
    field_simp
  have hDupper : (D : ℝ) ≤ Fintype.card V := by
    let : Nonempty V := Fintype.card_pos_iff.mp hnpos
    let x : V := Classical.choice (inferInstance : Nonempty V)
    have hh := G.degree_lt_card_verts x
    rw [hreg x] at hh
    exact_mod_cast hh.le
  have hu : (Fintype.card U : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
    have hh := (div_le_iff₀ hDpos).mp hρmax
    change 2 * (Fintype.card U : ℝ) ≤ (1 : ℝ) * D at hh
    linarith
  obtain ⟨Q⟩ := hN₁ V G D m hreg (by omega) hmn
  obtain ⟨I, hI0, hIcard, hIsub⟩ := nested_finsets_of_sizes (V := U)
    (floorOrbit ε (Fintype.card U)) rfl (floorOrbit_antitone he1 _)
  obtain ⟨_, _, hmargin⟩ := hN₂ m (by omega)
  have hstrong:∀i≤Q.length,0 < i →
      |2*((I i).card:ℝ)/initialIndexDensity U D-((D:ℝ)/Fintype.card V)*(Q.vertices i).card|≤β*(Q.vertices i).card ∧
      ∀x∈Q.vertices (i-(t+1)),
        |((G.neighborFinset x∩Q.vertices i).card:ℝ)-2*(I i).card/initialIndexDensity U D|≤β*(Q.vertices i).card:=by
    intro i hi hipos
    have herr := rounded_vortex_centre_error he.le heq hp hρmin hnpos hu hcentre i
    have hsmall : |2 * ((I i).card : ℝ) / ρ -
        ((D : ℝ) / Fintype.card V) * (Q.vertices i).card| ≤ β / 2 * (Q.vertices i).card := by
      have hlow : ε * m / 2 ≤ ((Q.vertices i).card : ℝ) := by
        have hsub := finset_chain_subset Q.vertices Q.length Q.nested hi (le_refl _)
        exact Q.terminal_lower.trans (by exact_mod_cast Finset.card_le_card hsub)
      have hbound : 3 / ρ₀ ≤ β / 2 * (Q.vertices i).card := by
        have hh := mul_le_mul_of_nonneg_left hlow hb.le
        nlinarith [hmargin]
      rw [hIcard i, Q.sizes i hi]
      exact herr.le.trans (by simpa only [Q.sizes i hi] using hbound)
    refine ⟨hsmall.trans ?_, ?_⟩
    · have hnonneg : (0 : ℝ) ≤ (Q.vertices i).card := by positivity
      nlinarith
    · intro x hx
      have hbase := Q.degrees_lookback i hi hipos x hx
      have ht := abs_sub_le ((G.neighborFinset x ∩ Q.vertices i).card : ℝ)
        (((D : ℝ) / Fintype.card V) * (Q.vertices i).card)
        (2 * ((I i).card : ℝ) / ρ)
      rw [abs_sub_comm (((D : ℝ) / Fintype.card V) * (Q.vertices i).card)] at ht
      dsimp only [ρ] at hsmall ht
      linarith
  have hbase:∀i≤Q.length,0 < i →
      |2*((I i).card:ℝ)/initialIndexDensity U D-((D:ℝ)/Fintype.card V)*(Q.vertices i).card|≤β*(Q.vertices i).card ∧
      ∀x∈Q.vertices (i-2),
        |((G.neighborFinset x∩Q.vertices i).card:ℝ)-2*(I i).card/initialIndexDensity U D|≤β*(Q.vertices i).card:=by
    intro i hi hipos
    obtain ⟨hfirst,hsecond⟩:=hstrong i hi hipos
    refine ⟨hfirst,?_⟩
    intro x hx
    exact hsecond x (finset_chain_subset Q.vertices Q.length Q.nested (by omega:i-(t+1) ≤ i-2) (by omega) hx)
  exact ⟨⟨⟨Q.toVertexVortex,I,hI0,hIcard,hIsub,hbase⟩,hstrong⟩⟩
end Oberwolfach
