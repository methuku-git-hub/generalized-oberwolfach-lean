module

public import Oberwolfach.FiniteSamplingMeasure

@[expose] public section

/-!
Bounded differences for finite independent categorical coordinates.
The proof uses finite sums and induction over the coordinates. It does
not impose independence on the derived tests.
-/
set_option autoImplicit false
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section
namespace Oberwolfach

theorem finiteLaw_nonempty
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) : Nonempty Ω := by
  by_contra h
  have : IsEmpty Ω := not_nonempty_iff.mp h
  have hh := μ.total
  simp at hh

theorem finiteLaw_expectation_const
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (c : ℝ) :
    μ.expectation (fun _ => c) = c := by
  simp only [FiniteLaw.expectation, ← Finset.sum_mul, μ.total, one_mul]

theorem finiteLaw_expectation_mono
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X Y : Ω → ℝ)
    (h : ∀ ω, X ω ≤ Y ω) : μ.expectation X ≤ μ.expectation Y :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

theorem finiteLaw_expectation_const_mul
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (c : ℝ) (X : Ω → ℝ) :
    μ.expectation (fun ω => c * X ω) = c * μ.expectation X := by
  unfold FiniteLaw.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem finiteLaw_expectation_difference
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X Y : Ω → ℝ) {c : ℝ}
    (h : ∀ ω, |X ω - Y ω| ≤ c) :
    |μ.expectation X - μ.expectation Y| ≤ c := by
  have heq : μ.expectation X - μ.expectation Y = μ.expectation (fun ω => X ω - Y ω) := by
    simp only [FiniteLaw.expectation, mul_sub, Finset.sum_sub_distrib]
  rw [heq, abs_le]
  constructor
  · have hh := finiteLaw_expectation_mono μ (fun _ => -c) (fun ω => X ω - Y ω)
      (fun ω => (abs_le.mp (h ω)).1)
    simpa only [finiteLaw_expectation_const] using hh
  · have hh := finiteLaw_expectation_mono μ (fun ω => X ω - Y ω) (fun _ => c)
      (fun ω => (abs_le.mp (h ω)).2)
    simpa only [finiteLaw_expectation_const] using hh

theorem finiteLaw_mgf_of_diameter
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hdiam : ∀ x y, |X x - X y| ≤ c) (t : ℝ) :
    μ.expectation (fun ω => Real.exp (t * (X ω - μ.expectation X))) ≤
      Real.exp (t ^ 2 * c ^ 2 / 8) := by
  classical
  let : MeasurableSpace Ω := ⊤
  have : Nonempty Ω := finiteLaw_nonempty μ
  obtain ⟨x, _, hmin⟩ := Finset.univ.exists_min_image X Finset.univ_nonempty
  have hbound : ∀ ω, X ω ∈ Set.Icc (X x) (X x + c) := by
    intro ω
    refine ⟨hmin ω (Finset.mem_univ ω), ?_⟩
    have hh := (abs_le.mp (hdiam ω x)).2
    linarith
  have hsub := hasSubgaussianMGF_of_mem_Icc
    (μ := μ.toPMF.toMeasure) (measurable_of_finite X).aemeasurable
    (Filter.Eventually.of_forall hbound)
  have hh := hsub.mgf_le t
  simp only [mgf, finiteLaw_integral] at hh
  have he : (((‖X x + c - X x‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2 =
      t ^ 2 * c ^ 2 / 8 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
      coe_nnnorm, Real.norm_eq_abs]
    rw [show X x + c - X x = c by ring, abs_of_nonneg hc]
    ring
  simpa only [he] using hh

theorem finiteLaw_pi_expectation_succ
    {n : ℕ} {State : Fin (n + 1) → Type*} [∀ i, Fintype (State i)]
    (μ : ∀ i, FiniteLaw (State i)) (X : (∀ i, State i) → ℝ) :
    (FiniteLaw.pi μ).expectation X =
      (μ 0).expectation (fun x =>
        (FiniteLaw.pi (fun i : Fin n => μ i.succ)).expectation
          (fun τ => X (Fin.cons x τ))) := by
  classical
  unfold FiniteLaw.expectation
  rw [← (Fin.consEquiv State).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  change (∏ i, (μ i).mass ((Fin.cons x τ) i)) * X (Fin.cons x τ) =
    (μ 0).mass x * ((∏ i : Fin n, (μ i.succ).mass (τ i)) * X (Fin.cons x τ))
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_assoc]

/-- The exponential bounded-differences estimate for the actual product
of the supplied categorical laws. Each coordinate has its own state type
and its own prescribed law. -/
theorem finiteLaw_boundedDifferences_mgf
    {n : ℕ} {State : Fin n → Type*} [∀ i, Fintype (State i)]
    (μ : ∀ i, FiniteLaw (State i)) (X : (∀ i, State i) → ℝ)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hchange : ∀ (i : Fin n) (σ τ : ∀ j, State j),
      (∀ j, j ≠ i → σ j = τ j) → |X σ - X τ| ≤ c i)
    (t : ℝ) :
    (FiniteLaw.pi μ).expectation (fun σ =>
      Real.exp (t * (X σ - (FiniteLaw.pi μ).expectation X))) ≤
      Real.exp (t ^ 2 * (∑ i, (c i) ^ 2) / 8) := by
  classical
  induction n with
  | zero =>
    let σ₀ : ∀ i : Fin 0, State i := fun i => Fin.elim0 i
    have hX : X = fun _ => X σ₀ := by
      funext σ
      exact congrArg X (Subsingleton.elim σ σ₀)
    rw [hX, finiteLaw_expectation_const]
    simp [finiteLaw_expectation_const]
  | succ n ih =>
    let ν := FiniteLaw.pi (fun i : Fin n => μ i.succ)
    let g (x : State 0) := ν.expectation (fun τ => X (Fin.cons x τ))
    have hmean : (FiniteLaw.pi μ).expectation X = (μ 0).expectation g :=
      finiteLaw_pi_expectation_succ μ X
    have htail (x : State 0) :
        ν.expectation (fun τ => Real.exp (t * (X (Fin.cons x τ) - g x))) ≤
          Real.exp (t ^ 2 * (∑ i : Fin n, (c i.succ) ^ 2) / 8) := by
      apply ih (fun i => μ i.succ) (fun τ => X (Fin.cons x τ))
        (fun i => c i.succ) (fun i => hc i.succ)
      intro i σ τ hagree
      apply hchange i.succ (Fin.cons x σ) (Fin.cons x τ)
      intro j hj
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        simp only [Fin.cons_succ]
        exact hagree j (fun h => hj (congrArg Fin.succ h))
    have hdiam (x y : State 0) : |g x - g y| ≤ c 0 := by
      apply finiteLaw_expectation_difference ν
      intro τ
      apply hchange 0 (Fin.cons x τ) (Fin.cons y τ)
      intro j hj
      cases j using Fin.cases with
      | zero => exact (hj rfl).elim
      | succ j => rfl
    have hhead := finiteLaw_mgf_of_diameter (μ 0) g (hc 0) hdiam t
    let A := Real.exp (t ^ 2 * (∑ i : Fin n, (c i.succ) ^ 2) / 8)
    have hfactor (x : State 0) :
        ν.expectation (fun τ => Real.exp (t * (X (Fin.cons x τ) -
          (FiniteLaw.pi μ).expectation X))) =
        Real.exp (t * (g x - (μ 0).expectation g)) *
          ν.expectation (fun τ => Real.exp (t * (X (Fin.cons x τ) - g x))) := by
      rw [← finiteLaw_expectation_const_mul]
      apply congrArg ν.expectation
      funext τ
      rw [← Real.exp_add, hmean]
      congr 1
      ring
    rw [finiteLaw_pi_expectation_succ]
    change (μ 0).expectation (fun x =>
      ν.expectation (fun τ => Real.exp (t * (X (Fin.cons x τ) -
        (FiniteLaw.pi μ).expectation X)))) ≤ _
    simp_rw [hfactor]
    calc
      _ ≤ (μ 0).expectation (fun x => A *
          Real.exp (t * (g x - (μ 0).expectation g))) := by
        apply finiteLaw_expectation_mono
        intro x
        have hh := mul_le_mul_of_nonneg_left (htail x)
          (Real.exp_pos (t * (g x - (μ 0).expectation g))).le
        simpa only [mul_comm] using hh
      _ = A * (μ 0).expectation (fun x =>
          Real.exp (t * (g x - (μ 0).expectation g))) :=
        finiteLaw_expectation_const_mul _ _ _
      _ ≤ A * Real.exp (t ^ 2 * (c 0) ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hhead (Real.exp_pos _).le
      _ = _ := by
        dsimp [A]
        rw [← Real.exp_add, Fin.sum_univ_succ]
        congr 1
        ring

theorem finiteLaw_boundedDifferences_tail
    {n : ℕ} {State : Fin n → Type*} [∀ i, Fintype (State i)]
    (μ : ∀ i, FiniteLaw (State i)) (X : (∀ i, State i) → ℝ)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hchange : ∀ (i : Fin n) (σ τ : ∀ j, State j),
      (∀ j, j ≠ i → σ j = τ j) → |X σ - X τ| ≤ c i)
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi μ).probability (fun σ =>
      t ≤ |X σ - (FiniteLaw.pi μ).expectation X|) ≤
      2 * Real.exp (-2 * t ^ 2 / (∑ i, (c i) ^ 2)) := by
  classical
  let : ∀ i, MeasurableSpace (State i) := fun _ => ⊤
  let q : ℝ≥0 := ⟨(∑ i, (c i) ^ 2) / 4,
    div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg (c i))) (by norm_num)⟩
  have hq : (q : ℝ) = (∑ i, (c i) ^ 2) / 4 := rfl
  have hsub : HasSubgaussianMGF
      (fun σ => X σ - (FiniteLaw.pi μ).expectation X) q
      (FiniteLaw.pi μ).toPMF.toMeasure := by
    refine ⟨fun _ => Integrable.of_finite, ?_⟩
    intro u
    have hh := finiteLaw_boundedDifferences_mgf μ X c hc hchange u
    simp only [mgf, finiteLaw_integral]
    convert hh using 1
    rw [hq]
    congr 1
    ring
  have hh := subgaussian_absolute_tail hsub ht
  rw [finiteLaw_probability_measure] at hh
  have he : -t ^ 2 / (2 * (q : ℝ)) = -2 * t ^ 2 / (∑ i, (c i) ^ 2) := by
    rw [hq]
    ring
  simpa only [he] using hh

theorem finiteLaw_pi_reindex_expectation
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {State : J → Type*} [∀ j, Fintype (State j)]
    (e : I ≃ J) (μ : ∀ j, FiniteLaw (State j)) (X : (∀ j, State j) → ℝ) :
    (FiniteLaw.pi μ).expectation X =
      (FiniteLaw.pi (fun i => μ (e i))).expectation
        (fun σ => X (Equiv.piCongrLeft State e σ)) := by
  classical
  unfold FiniteLaw.expectation
  rw [← (Equiv.piCongrLeft State e).sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  change (∏ j, (μ j).mass ((Equiv.piCongrLeft State e σ) j)) *
      X (Equiv.piCongrLeft State e σ) =
    (∏ i, (μ (e i)).mass (σ i)) * X (Equiv.piCongrLeft State e σ)
  rw [← e.prod_comp]
  simp only [Equiv.piCongrLeft_apply_apply]

theorem finiteLaw_probability_eq_expectation
    {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω) (B : Ω → Prop) [DecidablePred B] :
    ν.probability B = ν.expectation (fun ω => if B ω then 1 else 0) := by
  classical
  unfold FiniteLaw.probability FiniteLaw.expectation
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hb : B ω <;> simp [hb]

theorem finiteLaw_pi_reindex_probability
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {State : J → Type*} [∀ j, Fintype (State j)]
    (e : I ≃ J) (μ : ∀ j, FiniteLaw (State j)) (A : (∀ j, State j) → Prop) :
    (FiniteLaw.pi μ).probability A =
      (FiniteLaw.pi (fun i => μ (e i))).probability
        (fun σ => A (Equiv.piCongrLeft State e σ)) := by
  classical
  rw [finiteLaw_probability_eq_expectation, finiteLaw_probability_eq_expectation,
    finiteLaw_pi_reindex_expectation e μ]

/-- Bounded differences on any finite coordinate set. Reindexing transports
the given probability law exactly; it does not replace that law by a more
convenient sample. -/
theorem finiteLaw_boundedDifferences
    {E : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e, Fintype (State e)]
    (μ : ∀ e, FiniteLaw (State e)) (X : (∀ e, State e) → ℝ)
    (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hchange : ∀ (e : E) (σ τ : ∀ j, State j),
      (∀ j, j ≠ e → σ j = τ j) → |X σ - X τ| ≤ c e)
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi μ).probability (fun σ =>
      t ≤ |X σ - (FiniteLaw.pi μ).expectation X|) ≤
      2 * Real.exp (-2 * t ^ 2 / (∑ e, (c e) ^ 2)) := by
  classical
  let e := (Fintype.equivFin E).symm
  let P := Equiv.piCongrLeft State e
  have hch (i : Fin (Fintype.card E)) (σ τ : ∀ j, State (e j))
      (hagree : ∀ j, j ≠ i → σ j = τ j) :
      |X (P σ) - X (P τ)| ≤ c (e i) := by
    apply hchange (e i)
    intro j hj
    obtain ⟨k, rfl⟩ := e.surjective j
    change (Equiv.piCongrLeft State e σ) (e k) =
      (Equiv.piCongrLeft State e τ) (e k)
    simp only [Equiv.piCongrLeft_apply_apply]
    exact hagree k (fun h => hj (congrArg e h))
  have hh := finiteLaw_boundedDifferences_tail (fun i => μ (e i))
    (fun σ => X (P σ)) (fun i => c (e i)) (fun i => hc (e i)) hch ht
  rw [finiteLaw_pi_reindex_probability e μ, finiteLaw_pi_reindex_expectation e μ]
  have hsum : (∑ i : Fin (Fintype.card E), (c (e i)) ^ 2) = ∑ j, (c j) ^ 2 :=
    e.sum_comp (fun j => (c j) ^ 2)
  rw [hsum] at hh
  exact hh

theorem coordinatewise_constant
    {E : Type*} [Fintype E] [DecidableEq E] {State : E → Type*}
    (X : (∀ e, State e) → ℝ)
    (hchange : ∀ (e : E) (σ τ : ∀ j, State j),
      (∀ j, j ≠ e → σ j = τ j) → X σ = X τ) :
    ∀ σ τ, X σ = X τ := by
  classical
  have hstep (S : Finset E) : ∀ (σ τ : ∀ j, State j),
      (∀ j, j ∉ S → σ j = τ j) → X σ = X τ := by
    induction S using Finset.induction_on with
    | empty =>
      intro σ τ hagree
      exact congrArg X (funext (fun j => hagree j (by simp)))
    | @insert e S he ih =>
      intro σ τ hagree
      let σ' := Function.update σ e (τ e)
      have hfirst : X σ = X σ' := by
        apply hchange e
        intro j hj
        exact (Function.update_of_ne hj _ _).symm
      apply hfirst.trans
      apply ih σ' τ
      intro j hj
      by_cases hje : j = e
      · subst j
        exact Function.update_self _ _ _
      · change Function.update σ e (τ e) j = τ j
        rw [Function.update_of_ne hje]
        exact hagree j (by simp [hje, hj])
  exact fun σ τ => hstep Finset.univ σ τ (fun j hj => (hj (Finset.mem_univ j)).elim)

theorem finiteLaw_zero_boundedDifferences
    {E : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e, Fintype (State e)]
    (μ : ∀ e, FiniteLaw (State e)) (X : (∀ e, State e) → ℝ)
    (hchange : ∀ (e : E) (σ τ : ∀ j, State j),
      (∀ j, j ≠ e → σ j = τ j) → |X σ - X τ| ≤ 0) :
    ∀ σ, X σ = (FiniteLaw.pi μ).expectation X := by
  have hconst := coordinatewise_constant X (fun e σ τ h =>
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (hchange e σ τ h) (abs_nonneg _))))
  intro σ
  have heq : X = fun _ => X σ := funext (fun τ => hconst τ σ)
  rw [heq, finiteLaw_expectation_const]

/-- Concentration for a fixed root-omitted weighted sum. The influence
bound counts the supplied candidate occurrences separately and leaves the
weights and omitted roots unchanged. -/
theorem finiteLaw_omitted_weighted_tail
    {E : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e, Fintype (State e)]
    {I : Type*} (μ : ∀ e, FiniteLaw (State e))
    (C : Finset I) (F : I → Finset E) (R : Finset E)
    (s : I → ∀ e, State e) (w : I → ℝ) (b : E → ℝ)
    (hw : ∀ i ∈ C, 0 ≤ w i)
    (hload : ∀ e, (∑ i ∈ C, if e ∈ F i \ R then w i else 0) ≤ b e)
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi μ).probability (fun σ =>
      t ≤ |(∑ i ∈ C, w i * patternValue (F i \ R) (s i) σ) -
        (∑ i ∈ C, w i * ∏ e ∈ F i \ R, (μ e).mass (s i e))|) ≤
      2 * Real.exp (-2 * t ^ 2 / (∑ e, (b e) ^ 2)) := by
  classical
  let X (σ : ∀ e, State e) := ∑ i ∈ C, w i * patternValue (F i \ R) (s i) σ
  have hb (e : E) : 0 ≤ b e :=
    (Finset.sum_nonneg (fun i hi => by
      split_ifs
      · exact hw i hi
      · exact le_refl _)).trans (hload e)
  have hchange (e : E) (σ τ : ∀ j, State j)
      (hagree : ∀ j, j ≠ e → σ j = τ j) : |X σ - X τ| ≤ b e := by
    have hh := weighted_product_stability C (fun i => F i \ R) s w {e} τ σ hw
      (fun i _ j _ hj => (hagree j (by simpa only [Finset.mem_singleton] using hj)).symm)
    have hbase : |X σ - X τ| ≤ ∑ i ∈ C, if e ∈ F i \ R then w i else 0 := by
      simpa only [Finset.sum_singleton] using hh
    exact hbase.trans (hload e)
  have hh := finiteLaw_boundedDifferences μ X b hb hchange ht
  have hmean : (FiniteLaw.pi μ).expectation X =
      ∑ i ∈ C, w i * ∏ e ∈ F i \ R, (μ e).mass (s i e) :=
    finiteLaw_expectation_omitted_root_sum μ C F R s w
  simpa only [hmean, X] using hh

end Oberwolfach
