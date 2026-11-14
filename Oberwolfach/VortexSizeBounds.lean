module

public import Oberwolfach.VortexExtended

@[expose] public section

/-! Quantitative sizes of the vertex, index and difference domains used in completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem floorOrbit_scaled_le {ε : ℝ} (he : 0 ≤ ε) {u n a : ℕ}
    (h : a * u ≤ n) (i : ℕ) :
    a * floorOrbit ε u i ≤ floorOrbit ε n i := by
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [floorOrbit_succ, floorOrbit_succ]
    apply Nat.le_floor
    push_cast
    have hfloor := Nat.floor_le (show 0 ≤ ε * floorOrbit ε u i by positivity)
    have hcast : (a : ℝ) * floorOrbit ε u i ≤ floorOrbit ε n i := by exact_mod_cast ih
    have h₁ := mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg a)
    have h₂ := mul_le_mul_of_nonneg_left hcast he
    nlinarith

theorem regular_degree_le_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : ℕ} (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V) :
    D ≤ Fintype.card V := by
  let v : V := Classical.choice (Fintype.card_pos_iff.mp hn)
  have hh := G.degree_lt_card_verts v
  rw [hreg v] at hh
  exact hh.le

theorem Vortex.vertices_lower {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    {i : ℕ} (hi : i ≤ Q.length) :
    ε * m / 2 ≤ ((Q.vertices i).card : ℝ) := by
  exact Q.terminal_lower.trans (by
    exact_mod_cast Finset.card_le_card
      (finset_chain_subset Q.vertices Q.length Q.nested hi (le_refl _)))

theorem Vortex.index_size_upper {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hD : 0 < D) (he : 0 ≤ ε) (hρ : initialIndexDensity U D ≤ 1)
    {i : ℕ} (hi : i ≤ Q.length) :
    2 * (Q.indices i).card ≤ (Q.vertices i).card := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hinit : 2 * Fintype.card U ≤ Fintype.card V := by
    have hh := (div_le_iff₀ hD').mp hρ
    have hd := regular_degree_le_card hreg hn
    have hUr : (2 : ℝ) * Fintype.card U ≤ D := by simpa [initialIndexDensity] using hh
    have hUn : 2 * Fintype.card U ≤ D := by exact_mod_cast hUr
    omega
  rw [Q.index_sizes, Q.sizes i hi]
  exact floorOrbit_scaled_le he hinit i

theorem Vortex.index_size_lower {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε ρ₀ : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hD : (Fintype.card V : ℝ) / 2 ≤ D)
    (hρ₀ : 0 < ρ₀) (hρ : ρ₀ ≤ initialIndexDensity U D)
    (hb : 0 ≤ β) (hbq : β ≤ 1 / 4) {i : ℕ} (hi : i ≤ Q.length) :
    ρ₀ / 8 * (Q.vertices i).card ≤ ((Q.indices i).card : ℝ) := by
  have hp : 0 < initialIndexDensity U D := hρ₀.trans_le hρ
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : (1 / 2 : ℝ) ≤ (D : ℝ) / Fintype.card V :=
    (le_div_iff₀ hn').mpr (by linarith)
  have hc := (abs_le.mp (Q.estimates_including_zero hreg hn hp hb i hi).1).1
  have hnc : (0 : ℝ) ≤ (Q.vertices i).card := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hd hnc
  have hbmul := mul_le_mul_of_nonneg_right hbq hnc
  have hquarter : ((Q.vertices i).card : ℝ) / 4 ≤
      2 * (Q.indices i).card / initialIndexDensity U D := by linarith
  have hh := (le_div_iff₀ hp).mp hquarter
  have hhρ := mul_le_mul_of_nonneg_left hρ (show (0 : ℝ) ≤ (Q.vertices i).card / 4 by positivity)
  nlinarith

theorem Vortex.consecutive_size_bounds {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (he : 0 < ε) (hm : 0 < m) {i : ℕ} (hi : i < Q.length) :
    ε * (Q.vertices i).card / 2 ≤ ((Q.vertices (i + 1)).card : ℝ) ∧
    ((Q.vertices (i + 1)).card : ℝ) ≤ ε * (Q.vertices i).card := by
  have hrec : (Q.vertices (i + 1)).card = ⌊ε * (Q.vertices i).card⌋₊ := by
    rw [Q.sizes (i + 1) (by omega), floorOrbit_succ, Q.sizes i hi.le]
  have hpositive : 0 < (Q.vertices (i + 1)).card := by
    have hh := Q.vertices_lower (by omega : i + 1 ≤ Q.length)
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hh' : (0 : ℝ) < (Q.vertices (i + 1)).card := lt_of_lt_of_le (by positivity) hh
    exact_mod_cast hh'
  have hfloor := Nat.lt_floor_add_one (ε * (Q.vertices i).card)
  have hge : (1 : ℝ) ≤ (Q.vertices (i + 1)).card := by exact_mod_cast hpositive
  constructor
  · rw [← hrec] at hfloor
    linarith
  · rw [hrec]
    exact Nat.floor_le (by positivity)

theorem Vortex.extended_index_size_upper {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hD : 0 < D) (he : 0 ≤ ε) (hρ : initialIndexDensity U D ≤ 1) (i : ℕ) :
    2 * (Q.extendedIndices i).card ≤ (Q.extendedVertices i).card := by
  by_cases hi : i ≤ Q.length
  · rw [Q.extendedIndices_eq hi, Q.extendedVertices_eq hi]
    exact Q.index_size_upper hreg hn hD he hρ hi
  · rw [Q.extendedIndices_empty (by omega), Q.extendedVertices_empty (by omega)]
    simp

theorem Vortex.two_level_size_bound {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hD : 0 < D) (he : 0 ≤ ε) (hρ : initialIndexDensity U D ≤ 1)
    {i : ℕ} (hi : i < Q.length) :
    ((Q.extendedVertices (i + 2)).card : ℝ) + (Q.extendedIndices (i + 2)).card ≤
      2 * ε * (Q.vertices (i + 1)).card := by
  by_cases hi₂ : i + 2 ≤ Q.length
  · rw [Q.extendedIndices_eq hi₂, Q.extendedVertices_eq hi₂]
    have hu : (2 : ℝ) * (Q.indices (i + 2)).card ≤ (Q.vertices (i + 2)).card := by
      exact_mod_cast Q.index_size_upper hreg hn hD he hρ hi₂
    have hf : ((Q.vertices (i + 2)).card : ℝ) ≤ ε * (Q.vertices (i + 1)).card := by
      rw [Q.sizes (i + 2) hi₂, floorOrbit_succ, ← Q.sizes (i + 1) (by omega)]
      exact Nat.floor_le (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) (Q.vertices (i + 2)).card]
  · rw [Q.extendedIndices_empty (by omega), Q.extendedVertices_empty (by omega)]
    simp only [Finset.card_empty, Nat.cast_zero, zero_add]
    positivity

theorem Vortex.difference_size_lower {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (he : 0 ≤ ε) (heq : ε ≤ 1 / 4) {j k : ℕ}
    (hjk : j < k) (hk : k ≤ Q.length + 1) :
    3 * ε * m / 8 ≤ ((Q.extendedVertices j \ Q.extendedVertices k).card : ℝ) := by
  have hj : j ≤ Q.length := by omega
  have hl := Q.vertices_lower hj
  have hs := Q.extended_later_size_le_quarter he heq hjk
  rw [real_card_sdiff (Q.extendedVertices_subset hjk.le)]
  rw [Q.extendedVertices_eq hj] at hs ⊢
  linarith

end Oberwolfach
