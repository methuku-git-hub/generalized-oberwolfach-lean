module

public import Oberwolfach.VortexSizeBounds

@[expose] public section

/-! The numerical substitutions used on the fixed completion domains.
The degree estimates keep the ambient root, even when it is outside the domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem completion_difference_numeric {a b x d θ α β δ ρ ρ₀ : ℝ}
    (ha : 0 < a) (hp₀ : 0 < ρ₀) (hp : ρ₀ ≤ ρ) (hp1 : ρ ≤ 1)
    (hθ : 1 / 2 ≤ θ) (hα : 0 < α) (hd : θ + α ≤ d) (hd1 : d ≤ 1)
    (hb : 0 ≤ β) (hba : β ≤ α / 40) (hbd : β ≤ δ / 16)
    (hc : |2 * b / ρ - d * a| ≤ (5 / 3) * β * a)
    (hx : |x - 2 * b / ρ| ≤ (5 / 3) * β * a) :
    ρ₀ / 8 * a ≤ b ∧ b ≤ a ∧ a / 2 ≤ 2 * b / ρ ∧
      2 * b / ρ ≤ 2 * a ∧ |x - 2 * b / ρ| ≤ δ * a / 8 ∧
      (θ + α / 4) * a < x := by
  have hp' : 0 < ρ := hp₀.trans_le hp
  have hba' := mul_le_mul_of_nonneg_right hba ha.le
  have hbd' := mul_le_mul_of_nonneg_right hbd ha.le
  have hβa : 0 ≤ β * a := mul_nonneg hb ha.le
  have hd' := mul_le_mul_of_nonneg_right hd ha.le
  have hd1' := mul_le_mul_of_nonneg_right hd1 ha.le
  have hθ' := mul_le_mul_of_nonneg_right hθ ha.le
  obtain ⟨hcl, hcu⟩ := abs_le.mp hc
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  have hαa : 0 < α * a := mul_pos hα ha
  have hlow : a / 2 ≤ 2 * b / ρ := by nlinarith
  have hhigh : 2 * b / ρ ≤ 2 * a := by nlinarith
  have hbl := (le_div_iff₀ hp').mp hlow
  have hbu := (div_le_iff₀ hp').mp hhigh
  have hpLow := mul_le_mul_of_nonneg_right hp ha.le
  have hpHigh := mul_le_mul_of_nonneg_right hp1 ha.le
  refine ⟨by nlinarith, by nlinarith, hlow, hhigh, ?_, ?_⟩
  · exact hx.trans (by nlinarith)
  · nlinarith

theorem Vortex.completion_difference_estimates {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε θ α δ ρ₀ : ℝ}
    (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hm : 0 < m) (he : 0 < ε) (heq : ε ≤ 1 / 4)
    (hp₀ : 0 < ρ₀) (hp : ρ₀ ≤ initialIndexDensity U D)
    (hp1 : initialIndexDensity U D ≤ 1)
    (hθ : 1 / 2 ≤ θ) (hα : 0 < α)
    (hd : θ + α ≤ (D : ℝ) / Fintype.card V)
    (hb : 0 ≤ β) (hba : β ≤ α / 40) (hbd : β ≤ δ / 16)
    {j k : ℕ} (hjk : j < k) (hk : k ≤ Q.length + 1)
    (x : V) (hx : x ∈ Q.extendedVertices (k - 2)) :
    let A := Q.extendedVertices j \ Q.extendedVertices k
    let B := Q.extendedIndices j \ Q.extendedIndices k
    ρ₀ / 8 * A.card ≤ (B.card : ℝ) ∧ (B.card : ℝ) ≤ A.card ∧
      (A.card : ℝ) / 2 ≤ 2 * B.card / initialIndexDensity U D ∧
      2 * (B.card : ℝ) / initialIndexDensity U D ≤ 2 * A.card ∧
      |((G.neighborFinset x ∩ A).card : ℝ) -
        2 * B.card / initialIndexDensity U D| ≤ δ * A.card / 8 ∧
      (θ + α / 4) * A.card < ((G.neighborFinset x ∩ A).card : ℝ) := by
  dsimp only
  have hsize := Q.difference_size_lower he.le heq hjk hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : (0 : ℝ) < (Q.extendedVertices j \ Q.extendedVertices k).card :=
    lt_of_lt_of_le (by positivity) hsize
  have hd1 : (D : ℝ) / Fintype.card V ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hn : (0 : ℝ) < Fintype.card V)).mpr
    exact_mod_cast regular_degree_le_card hreg hn
  obtain ⟨hc, hx'⟩ := Q.extended_difference_degree_estimates hreg hn
    (hp₀.trans_le hp) hb he.le heq hjk x hx
  exact completion_difference_numeric ha hp₀ hp hp1 hθ hα hd hd1 hb hba hbd hc hx'

theorem Vortex.local_degree_margin {V U : Type*} [Fintype V] [Fintype U]
    {G : SimpleGraph V} {D m : ℕ} {β ε θ α : ℝ}
    (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hm : 0 < m) (he : 0 < ε) (hp : 0 < initialIndexDensity U D)
    (hα : 0 < α) (hd : θ + α ≤ (D : ℝ) / Fintype.card V)
    (hb : 0 ≤ β) (hba : β ≤ α / 40)
    {i j : ℕ} (hj : j ≤ Q.length) (hji : j ≤ i + 2)
    (x : V) (hx : x ∈ Q.vertices i) (hi : i ≤ Q.length) :
    (θ + α / 4) * (Q.vertices j).card <
      ((G.neighborFinset x ∩ Q.vertices j).card : ℝ) := by
  have hxj : x ∈ Q.vertices (j - 2) :=
    finset_chain_subset Q.vertices Q.length Q.nested (by omega) hi hx
  obtain ⟨hc, hx'⟩ := Q.estimates_including_zero hreg hn hp hb j hj
  have hcl := (abs_le.mp hc).1
  have hxl := (abs_le.mp (hx' x hxj)).1
  have hsize := Q.vertices_lower hj
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : (0 : ℝ) < (Q.vertices j).card := lt_of_lt_of_le (by positivity) hsize
  have hba' := mul_le_mul_of_nonneg_right hba ha.le
  have hd' := mul_le_mul_of_nonneg_right hd ha.le
  have hαa := mul_pos hα ha
  nlinarith

end Oberwolfach
