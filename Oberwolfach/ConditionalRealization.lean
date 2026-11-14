module

public import Oberwolfach.FiniteUniform
public import Oberwolfach.FiniteSamplingMeasure

@[expose] public section

/-! Conditional realization of compatible finite marginals. The boundary law
is fixed and every interval law is recovered exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_mass_le_map {P B : Type*} [Fintype P] [Fintype B]
    (μ : FiniteLaw P) (f : P → B) (p : P) :
    μ.mass p ≤ (μ.map f).mass (f p) := by
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun q => if f q = f p then μ.mass q else 0)
    (fun q _ => by split_ifs; exact μ.nonneg q; exact le_refl _) (Finset.mem_univ p)
  simpa only [ite_true, FiniteLaw.map] using hh

def FiniteLaw.conditionOnMap {P B : Type*} [Fintype P] [Fintype B]
    (μ : FiniteLaw P) (f : P → B) (b : B) : FiniteLaw P := by
  classical
  by_cases hz : (μ.map f).mass b = 0
  · exact μ
  · exact {
      mass p := if f p = b then μ.mass p / (μ.map f).mass b else 0
      nonneg p := by
        split_ifs
        · exact div_nonneg (μ.nonneg p) ((μ.map f).nonneg b)
        · exact le_refl _
      total := by
        have hh (p : P) : (if f p = b then μ.mass p / (μ.map f).mass b else 0) =
            (if f p = b then μ.mass p else 0) / (μ.map f).mass b := by
          split_ifs <;> simp
        simp_rw [hh]
        rw [← Finset.sum_div]
        exact div_self hz }

theorem finiteLaw_conditionOnMap_weight {P B : Type*} [Fintype P] [Fintype B]
    (μ : FiniteLaw P) (f : P → B) (b : B) (p : P) :
    (μ.map f).mass b * (μ.conditionOnMap f b).mass p =
      if f p = b then μ.mass p else 0 := by
  by_cases hz : (μ.map f).mass b = 0
  · simp only [hz, zero_mul]
    by_cases hp : f p = b
    · have hh := finiteLaw_mass_le_map μ f p
      rw [hp, hz] at hh
      simp only [hp, ite_true]
      exact (le_antisymm hh (μ.nonneg p)).symm
    · simp only [hp, ite_false]
  · simp only [FiniteLaw.conditionOnMap, hz, dite_false]
    by_cases hp : f p = b
    · simp only [hp, ite_true]
      exact mul_div_cancel₀ _ hz
    · simp only [hp, ite_false, mul_zero]

theorem finiteLaw_conditionOnMap_reconstruct {T P B : Type*}
    [Fintype T] [Fintype P] [Fintype B]
    (ν : FiniteLaw T) (μ : FiniteLaw P) (g : T → B) (f : P → B)
    (h : ν.map g = μ.map f) (p : P) :
    (∑ t, ν.mass t * (μ.conditionOnMap f (g t)).mass p) = μ.mass p := by
  change ν.expectation (fun t => (μ.conditionOnMap f (g t)).mass p) = _
  rw [← finiteLaw_map_expectation ν g (fun b => (μ.conditionOnMap f b).mass p), h]
  unfold FiniteLaw.expectation
  simp_rw [finiteLaw_conditionOnMap_weight]
  simp

theorem finiteLaw_pi_coordinate_probability {I : Type*} [Fintype I] [DecidableEq I]
    {P : I → Type*} [∀ i, Fintype (P i)]
    (μ : ∀ i, FiniteLaw (P i)) (i : I) (p : P i) :
    (FiniteLaw.pi μ).probability (fun σ => σ i = p) = (μ i).mass p := by
  let : ∀ i, MeasurableSpace (P i) := fun _ => ⊤
  let : ∀ i, MeasurableSingletonClass (P i) := fun _ => ⟨fun _ => trivial⟩
  have hh := finiteLaw_coordinate_expectation μ i (fun q => if q = p then 1 else 0)
  simpa [FiniteLaw.expectation, FiniteLaw.probability, mul_ite] using hh

theorem finiteLaw_conditional_realization_with_formula
    {T I : Type*} [Fintype T] [Fintype I] [DecidableEq I]
    {P B : I → Type*} [∀ i, Fintype (P i)] [∀ i, Fintype (B i)]
    (ν : FiniteLaw T) (μ : ∀ i, FiniteLaw (P i))
    (g : ∀ i, T → B i) (f : ∀ i, P i → B i)
    (h : ∀ i, ν.map (g i) = (μ i).map (f i)) :
    ∃ Ω : FiniteLaw (Σ _ : T, ∀ i, P i),
      (∀ t, (∑ σ, Ω.mass ⟨t, σ⟩) = ν.mass t) ∧
      (∀ i p, Ω.probability (fun z => z.2 i = p) = (μ i).mass p) ∧
      (∀ t σ, 0 < Ω.mass ⟨t, σ⟩ → ∀ i, f i (σ i) = g i t) ∧
      (∀ t σ, Ω.mass ⟨t, σ⟩ = ν.mass t *
        ∏ i, ((μ i).conditionOnMap (f i) (g i t)).mass (σ i)) := by
  let κ (t : T) (i : I) := (μ i).conditionOnMap (f i) (g i t)
  let Ω := ν.sigma (fun t => FiniteLaw.pi (κ t))
  refine ⟨Ω, ?_, ?_, ?_, ?_⟩
  · intro t
    change (∑ σ, ν.mass t * (FiniteLaw.pi (κ t)).mass σ) = _
    rw [← Finset.mul_sum, (FiniteLaw.pi (κ t)).total, mul_one]
  · intro i p
    change (∑ z : (Σ _ : T, ∀ i, P i), if z.2 i = p then
      ν.mass z.1 * (FiniteLaw.pi (κ z.1)).mass z.2 else 0) = _
    rw [Fintype.sum_sigma]
    have hh (t : T) :
        (∑ σ, if σ i = p then ν.mass t * (FiniteLaw.pi (κ t)).mass σ else 0) =
        ν.mass t * (κ t i).mass p := by
      rw [← finiteLaw_pi_coordinate_probability (κ t) i p]
      unfold FiniteLaw.probability
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      split_ifs <;> simp
    simp_rw [hh]
    exact finiteLaw_conditionOnMap_reconstruct ν (μ i) (g i) (f i) (h i) p
  · intro t σ hpos i
    by_contra hbad
    have hv : 0 < ν.mass t := by
      have hh := (mul_pos_iff.mp hpos)
      rcases hh with ⟨hv, _⟩ | ⟨hv, _⟩
      · exact hv
      · exact False.elim ((not_lt_of_ge (ν.nonneg t)) hv)
    have hK : 0 < ((μ i).map (f i)).mass (g i t) := by
      rw [← h i]
      exact hv.trans_le (finiteLaw_mass_le_map ν (g i) t)
    have hz : (κ t i).mass (σ i) = 0 := by
      dsimp only [κ]
      simp only [FiniteLaw.conditionOnMap, hK.ne', dite_false, hbad, ite_false]
    have hprod : (FiniteLaw.pi (κ t)).mass σ = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    change 0 < ν.mass t * (FiniteLaw.pi (κ t)).mass σ at hpos
    rw [hprod, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  · intro t σ
    rfl

theorem finiteLaw_conditional_realization
    {T I : Type*} [Fintype T] [Fintype I] [DecidableEq I]
    {P B : I → Type*} [∀ i, Fintype (P i)] [∀ i, Fintype (B i)]
    (ν : FiniteLaw T) (μ : ∀ i, FiniteLaw (P i))
    (g : ∀ i, T → B i) (f : ∀ i, P i → B i)
    (h : ∀ i, ν.map (g i) = (μ i).map (f i)) :
    ∃ Ω : FiniteLaw (Σ _ : T, ∀ i, P i),
      (∀ t, (∑ σ, Ω.mass ⟨t, σ⟩) = ν.mass t) ∧
      (∀ i p, Ω.probability (fun z => z.2 i = p) = (μ i).mass p) ∧
      (∀ t σ, 0 < Ω.mass ⟨t, σ⟩ → ∀ i, f i (σ i) = g i t) := by
  obtain ⟨Ω, hb, hp, hs, _⟩ := finiteLaw_conditional_realization_with_formula ν μ g f h
  exact ⟨Ω, hb, hp, hs⟩

theorem weighted_conditional_realization_with_formula
    {T I : Type*} [Fintype T] [Fintype I] [DecidableEq I]
    {P E : I → Type*} [∀ i, Fintype (P i)] [∀ i, Fintype (E i)]
    (J : T → ℝ) (w : ∀ i, P i → ℝ) (B : ℝ) (hB : 0 < B)
    (hJ : ∀ t, 0 ≤ J t) (hw : ∀ i p, 0 ≤ w i p)
    (hJsum : ∑ t, J t = B) (hwsum : ∀ i, ∑ p, w i p = B)
    (g : ∀ i, T → E i) (f : ∀ i, P i → E i)
    (hmarg : ∀ i e, (∑ t, if g i t = e then J t else 0) =
      ∑ p, if f i p = e then w i p else 0) :
    ∃ W : (Σ _ : T, ∀ i, P i) → ℝ,
      (∀ z, 0 ≤ W z) ∧ (∑ z, W z) = B ∧
      (∀ t, (∑ σ, W ⟨t, σ⟩) = J t) ∧
      (∀ i p, (∑ z, if z.2 i = p then W z else 0) = w i p) ∧
      (∀ t σ, 0 < W ⟨t, σ⟩ → ∀ i, f i (σ i) = g i t) ∧
      (∀ t σ, W ⟨t, σ⟩ = J t * ∏ i,
        if f i (σ i) = g i t then
          w i (σ i) / (∑ p, if f i p = g i t then w i p else 0) else 0) := by
  let ν : FiniteLaw T := {
    mass t := J t / B
    nonneg t := div_nonneg (hJ t) hB.le
    total := by rw [← Finset.sum_div, hJsum, div_self hB.ne'] }
  let μ (i : I) : FiniteLaw (P i) := {
    mass p := w i p / B
    nonneg p := div_nonneg (hw i p) hB.le
    total := by rw [← Finset.sum_div, hwsum i, div_self hB.ne'] }
  have hm (i : I) : ν.map (g i) = (μ i).map (f i) := by
    apply finiteLaw_ext
    intro e
    change (∑ t, if g i t = e then J t / B else 0) =
      ∑ p, if f i p = e then w i p / B else 0
    have hid (a : ℝ) (b : Prop) [Decidable b] :
        (if b then a / B else 0) = (if b then a else 0) / B := by
      split_ifs <;> simp
    simp_rw [hid, ← Finset.sum_div]
    rw [hmarg i e]
  obtain ⟨Ω, hboundary, hpaths, hsupport, hformula⟩ :=
    finiteLaw_conditional_realization_with_formula ν μ g f hm
  refine ⟨fun z => B * Ω.mass z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonneg hB.le (Ω.nonneg z)
  · rw [← Finset.mul_sum, Ω.total, mul_one]
  · intro t
    rw [← Finset.mul_sum, hboundary]
    exact mul_div_cancel₀ _ hB.ne'
  · intro i p
    have heq (z : Σ _ : T, ∀ i, P i) :
        (if z.2 i = p then B * Ω.mass z else 0) =
        B * (if z.2 i = p then Ω.mass z else 0) := by
      split_ifs <;> simp
    simp_rw [heq]
    rw [← Finset.mul_sum]
    change B * Ω.probability (fun z => z.2 i = p) = _
    rw [hpaths i p]
    exact mul_div_cancel₀ _ hB.ne'
  · intro t σ hp
    exact hsupport t σ ((mul_pos_iff_of_pos_left hB).mp hp)
  · intro t σ
    change B * Ω.mass ⟨t, σ⟩ = _
    rw [hformula]
    change B * (J t / B * _) = _
    rw [← mul_assoc, mul_div_cancel₀ _ hB.ne']
    by_cases hzero : J t = 0
    · simp only [hzero, zero_mul]
    · apply congrArg (fun z => J t * z)
      apply Finset.prod_congr rfl
      intro i _
      have hJpos : 0 < J t := lt_of_le_of_ne (hJ t) (Ne.symm hzero)
      have hKpos : 0 < ((μ i).map (f i)).mass (g i t) := by
        rw [← hm i]
        exact (div_pos hJpos hB).trans_le (finiteLaw_mass_le_map ν (g i) t)
      have hKform : ((μ i).map (f i)).mass (g i t) =
          (∑ p, if f i p = g i t then w i p else 0) / B := by
        change (∑ p, if f i p = g i t then w i p / B else 0) = _
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro p _
        split_ifs <;> simp
      have hc : ((μ i).conditionOnMap (f i) (g i t)).mass (σ i) =
          (if f i (σ i) = g i t then (μ i).mass (σ i) else 0) /
            ((μ i).map (f i)).mass (g i t) := by
        apply (eq_div_iff hKpos.ne').mpr
        simpa only [mul_comm] using finiteLaw_conditionOnMap_weight (μ i) (f i) (g i t) (σ i)
      rw [hc, hKform]
      by_cases he : f i (σ i) = g i t
      · simp only [he, ite_true]
        exact div_div_div_cancel_right₀ hB.ne' _ _
      · simp only [he, ite_false, zero_div]

theorem weighted_conditional_realization
    {T I : Type*} [Fintype T] [Fintype I] [DecidableEq I]
    {P E : I → Type*} [∀ i, Fintype (P i)] [∀ i, Fintype (E i)]
    (J : T → ℝ) (w : ∀ i, P i → ℝ) (B : ℝ) (hB : 0 < B)
    (hJ : ∀ t, 0 ≤ J t) (hw : ∀ i p, 0 ≤ w i p)
    (hJsum : ∑ t, J t = B) (hwsum : ∀ i, ∑ p, w i p = B)
    (g : ∀ i, T → E i) (f : ∀ i, P i → E i)
    (hmarg : ∀ i e, (∑ t, if g i t = e then J t else 0) =
      ∑ p, if f i p = e then w i p else 0) :
    ∃ W : (Σ _ : T, ∀ i, P i) → ℝ,
      (∀ z, 0 ≤ W z) ∧ (∑ z, W z) = B ∧
      (∀ t, (∑ σ, W ⟨t, σ⟩) = J t) ∧
      (∀ i p, (∑ z, if z.2 i = p then W z else 0) = w i p) ∧
      (∀ t σ, 0 < W ⟨t, σ⟩ → ∀ i, f i (σ i) = g i t) := by
  obtain ⟨W, hW, ht, hb, hp, hs, _⟩ :=
    weighted_conditional_realization_with_formula J w B hB hJ hw hJsum hwsum g f hmarg
  exact ⟨W, hW, ht, hb, hp, hs⟩

end Oberwolfach
