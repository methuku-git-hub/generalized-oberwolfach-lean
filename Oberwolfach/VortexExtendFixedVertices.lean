module

public import Oberwolfach.Vortex

@[expose] public section
/-! Extend a previously chosen physical vertex vortex by a class-specific
nested sequence of factor indices, without changing the vertex sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe b c

theorem vortex_extend_fixed_vertices {β ε ρ₀ : ℝ} (hb : 0 < β) (he : 0 < ε)
    (heq : ε < 1 / 4) (hp : 0 < ρ₀) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ (V : Type b) [Fintype V] (U : Type c) [Fintype U]
      (G : SimpleGraph V) (D m : ℕ),
      G.IsRegularOfDegree D → (Fintype.card V : ℝ) / 2 ≤ D →
      ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D ≤ 1 →
      m₀ ≤ m → m ≤ Fintype.card V →
      ∀ Q : VertexVortex G D (β / 2) ε m,
      ∃ Q' : Vortex U G D β ε m, Q'.toVertexVortex = Q := by
  have he1 : ε < 1 := by linarith
  obtain ⟨N₂, hN₂1, hN₂⟩ := eventually_vortex_error_budget hb he he1 hp
  refine ⟨N₂, hN₂1, ?_⟩
  intro V _ U _ G D m hreg hDmin hρmin hρmax hm hmn Q
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
  obtain ⟨I, hI0, hIcard, hIsub⟩ := nested_finsets_of_sizes (V := U)
    (floorOrbit ε (Fintype.card U)) rfl (floorOrbit_antitone he1 _)
  obtain ⟨_, _, hmargin⟩ := hN₂ m (by omega)
  refine ⟨{
    toVertexVortex := Q
    indices := I
    indices_initial := hI0
    index_sizes := hIcard
    indices_nested := hIsub
    centre_estimates := ?_ }, rfl⟩
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
    have hbase := Q.degrees i hi hipos x hx
    have ht := abs_sub_le ((G.neighborFinset x ∩ Q.vertices i).card : ℝ)
      (((D : ℝ) / Fintype.card V) * (Q.vertices i).card)
      (2 * ((I i).card : ℝ) / ρ)
    rw [abs_sub_comm (((D : ℝ) / Fintype.card V) * (Q.vertices i).card)] at ht
    dsimp only [ρ] at hsmall ht
    linarith

end Oberwolfach
