module

public import Oberwolfach.DifferenceDomains

@[expose] public section

/-! The vortex estimates at level zero and on differences used by cover-down. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem Vortex.estimates_including_zero {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hρ : 0 < initialIndexDensity U D) (hb : 0 ≤ β)
    (i : ℕ) (hi : i ≤ Q.length) :
    |2 * ((Q.indices i).card : ℝ) / initialIndexDensity U D -
      ((D : ℝ) / Fintype.card V) * (Q.vertices i).card| ≤ β * (Q.vertices i).card ∧
    ∀ x ∈ Q.vertices (i - 2),
      |((G.neighborFinset x ∩ Q.vertices i).card : ℝ) -
        2 * (Q.indices i).card / initialIndexDensity U D| ≤ β * (Q.vertices i).card := by
  by_cases hz : i = 0
  · subst i
    have hD : (D : ℝ) ≠ 0 := by
      intro h
      simp [initialIndexDensity, h] at hρ
    have hU : (Fintype.card U : ℝ) ≠ 0 := by
      intro h
      simp [initialIndexDensity, h] at hρ
    have hcentre : 2 * (Fintype.card U : ℝ) / initialIndexDensity U D = D := by
      dsimp only [initialIndexDensity]
      field_simp
    have hn' : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Q.initial, Q.indices_initial, Finset.card_univ, Finset.card_univ, hcentre,
      div_mul_cancel₀ _ hn', sub_self, abs_zero]
    refine ⟨by positivity, ?_⟩
    intro x hx
    rw [Finset.inter_univ, SimpleGraph.card_neighborFinset_eq_degree, hreg x,
      sub_self, abs_zero]
    positivity
  · exact Q.centre_estimates i hi (by omega)

theorem Vortex.later_size_le_quarter {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (he : 0 ≤ ε) (heq : ε ≤ 1 / 4) {j k : ℕ} (hjk : j < k) (hk : k ≤ Q.length) :
    ((Q.vertices k).card : ℝ) ≤ (Q.vertices j).card / 4 := by
  have hsub := finset_chain_subset Q.vertices Q.length Q.nested
    (by omega : j + 1 ≤ k) hk
  have hsmall : ((Q.vertices k).card : ℝ) ≤ (Q.vertices (j + 1)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hf : ((Q.vertices (j + 1)).card : ℝ) ≤ ε * (Q.vertices j).card := by
    rw [Q.sizes (j + 1) (by omega), floorOrbit_succ, ← Q.sizes j (by omega)]
    exact Nat.floor_le (mul_nonneg he (Nat.cast_nonneg _))
  have hh := mul_le_mul_of_nonneg_right heq (Nat.cast_nonneg (Q.vertices j).card)
  linarith

theorem Vortex.difference_degree_estimates {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hρ : 0 < initialIndexDensity U D) (hb : 0 ≤ β)
    (he : 0 ≤ ε) (heq : ε ≤ 1 / 4) {j k : ℕ} (hjk : j < k) (hk : k ≤ Q.length)
    (x : V) (hx : x ∈ Q.vertices (k - 2)) :
    |2 * ((Q.indices j \ Q.indices k).card : ℝ) / initialIndexDensity U D -
        ((D : ℝ) / Fintype.card V) * (Q.vertices j \ Q.vertices k).card| ≤
      (5 / 3 : ℝ) * β * (Q.vertices j \ Q.vertices k).card ∧
    |((G.neighborFinset x ∩ (Q.vertices j \ Q.vertices k)).card : ℝ) -
        2 * (Q.indices j \ Q.indices k).card / initialIndexDensity U D| ≤
      (5 / 3 : ℝ) * β * (Q.vertices j \ Q.vertices k).card := by
  classical
  have hj : j ≤ Q.length := by omega
  have hxj : x ∈ Q.vertices (j - 2) :=
    finset_chain_subset Q.vertices Q.length Q.nested (by omega : j - 2 ≤ k - 2)
      (by omega) hx
  have hA := Q.estimates_including_zero hreg hn hρ hb j hj
  have hB := Q.estimates_including_zero hreg hn hρ hb k hk
  exact nested_domains_degree_subtraction G
    (finset_chain_subset Q.vertices Q.length Q.nested hjk.le hk)
    (finset_chain_subset Q.indices k (fun i _ => Q.indices_nested i) hjk.le (le_refl k))
    β (initialIndexDensity U D) ((D : ℝ) / Fintype.card V) hb
    (Q.later_size_le_quarter he heq hjk hk) hA.1 hB.1 x (hA.2 x hxj) (hB.2 x hx)

end Oberwolfach
