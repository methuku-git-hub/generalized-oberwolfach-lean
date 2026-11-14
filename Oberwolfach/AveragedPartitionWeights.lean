module

public import Oberwolfach.PartitionWeightData
public import Oberwolfach.GoodAveraging
public import Oberwolfach.EqualCellPartitions
public import Oberwolfach.SuccessorWeightScale

@[expose] public section

/-! Preliminary successor weights: average over the original ordered
partition law, put zero on bad partitions, and divide by the exact
probability of placing the two specified auxiliary endpoints. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def maskWeight {Ω T : Type*} (Good : Ω → Prop) (w : Ω → T → ℝ) (ω : Ω) (t : T) : ℝ :=
  if Good ω then w ω t else 0

section
variable {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
variable [Nonempty (FixedPartition V k d)]
variable (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V)
variable (a : (Fin (ℓ + 2) ⊕ Fin (ℓ + 2)) ↪ Fin k)
variable (Good : FixedPartition V k d → Prop)
variable (w : FixedPartition V k d → (Fin (ℓ + 2) → V × V) → ℝ)
variable (p q A B : ℝ)
variable (hw : ∀ P, Good P → PartitionTupleWeightConditions G σ P a p q A B (w P))

include hw in
theorem averagedPartition_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) (t : Fin (ℓ + 2) → V × V) :
    0 ≤ averagedWeight (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w) ρ t := by
  apply averagedWeight_nonneg _ _ hρ
  intro P s
  unfold maskWeight
  split_ifs with hg
  · exact (hw P hg).nonneg s
  · exact le_rfl

include hw in
theorem averagedPartition_invalid_zero (ρ : ℝ) (t : Fin (ℓ + 2) → V × V)
    (ht : ¬ TwistedCyclicTupleValid G σ t) :
    averagedWeight (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w) ρ t = 0 := by
  apply averagedWeight_zero_off_support _ _ ρ (TwistedCyclicTupleValid G σ) _ t ht
  intro P s hs
  unfold maskWeight
  split_ifs with hg
  · apply le_antisymm _ ((hw P hg).nonneg s)
    exact le_of_not_gt (fun hp => hs ((hw P hg).support s hp).1)
  · rfl

include hw in
theorem averagedPartition_left_edge (m : ℕ) (hm : ∀ i, d (a i) = m)
    (δ ε : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (hρ : 0 < successorPairProbability m (Fintype.card V))
    (hgood : 1-δ ≤ (FiniteLaw.uniform (FixedPartition V k d)).probability Good)
    (hscale : δ ≤ ε * successorPairProbability m (Fintype.card V))
    (i : Fin (ℓ + 2)) (x y : V) (hxy : x ≠ y) (hG : G.Adj x y) :
    1-p-ε ≤ (∑ t, if t i = (x,y) then
      averagedWeight (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w)
        (successorPairProbability m (Fintype.card V)) t else 0) ∧
    (∑ t, if t i = (x,y) then
      averagedWeight (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w)
        (successorPairProbability m (Fintype.card V)) t else 0) ≤ 1 := by
  let E (P : FixedPartition V k d) := P.1 x = a (Sum.inl i) ∧ P.1 y = a (Sum.inr i)
  have hresult := averagedWeight_good_edge_bounds (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w) (fun t => t i = (x,y)) E Good
    _ δ p ε hρ hp hp1 hε (by
      have he := fixedPartition_two_placement (d := d) x y hxy (a (Sum.inl i)) (a (Sum.inr i))
        (by intro h; have hh := a.injective h; cases hh)
      simpa only [hm, successorPairProbability, pow_two] using he) hgood hscale (by
    intro P
    by_cases hg : Good P
    · have h := (hw P hg).left i x y
      simp only [maskWeight, hg, ite_true, and_true, hG, mul_ite, mul_one, mul_zero, E] at h ⊢
      convert h using 2 <;> first | (apply Finset.sum_congr rfl; intro t _; split_ifs <;> rfl) | (split_ifs <;> rfl)
    · simp only [maskWeight, hg, ite_false, and_false, ite_self, Finset.sum_const_zero]
      constructor
      · exact le_rfl
      · split_ifs <;> norm_num)
  convert hresult using 2 <;> apply Finset.sum_congr rfl <;> intro t _ <;> split_ifs <;> rfl

include hw in
theorem averagedPartition_right_edge (m : ℕ) (hm : ∀ i, d (a i) = m)
    (δ ε : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (hρ : 0 < successorPairProbability m (Fintype.card V))
    (hgood : 1-δ ≤ (FiniteLaw.uniform (FixedPartition V k d)).probability Good)
    (hscale : δ ≤ ε * successorPairProbability m (Fintype.card V))
    (i : Fin (ℓ + 2)) (x y : V) (hxy : x ≠ y) (hG : G.Adj x (σ i y)) :
    1-p-ε ≤ (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y) then
      averagedWeight (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w)
        (successorPairProbability m (Fintype.card V)) t else 0) ∧
    (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y) then
      averagedWeight (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w)
        (successorPairProbability m (Fintype.card V)) t else 0) ≤ 1 := by
  let E (P : FixedPartition V k d) := P.1 x = a (Sum.inr i) ∧
    P.1 y = a (Sum.inl (finRotate (ℓ + 2) i))
  have hresult := averagedWeight_good_edge_bounds (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w) (fun t => ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y)) E Good
    _ δ p ε hρ hp hp1 hε (by
      have he := fixedPartition_two_placement (d := d) x y hxy (a (Sum.inr i))
        (a (Sum.inl (finRotate (ℓ + 2) i))) (by intro h; have hh := a.injective h; cases hh)
      simpa only [hm, successorPairProbability, pow_two] using he) hgood hscale (by
    intro P
    by_cases hg : Good P
    · have h := (hw P hg).right i x y
      simp only [maskWeight, hg, ite_true, and_true, hG, mul_ite, mul_one, mul_zero, E] at h ⊢
      convert h using 2 <;> first | (apply Finset.sum_congr rfl; intro t _; split_ifs <;> rfl) | (split_ifs <;> rfl)
    · simp only [maskWeight, hg, ite_false, and_false, ite_self, Finset.sum_const_zero]
      constructor
      · exact le_rfl
      · split_ifs <;> norm_num)
  convert hresult using 2 <;> apply Finset.sum_congr rfl <;> intro t _ <;> split_ifs <;> rfl

include hw in
theorem averagedPartition_positions (m : ℕ) (hm : ∀ i, d (a i) = m)
    (δ ρ : ℝ) (hρ : 0 < ρ) (hq : 0 ≤ q)
    (hgood : 1-δ ≤ (FiniteLaw.uniform (FixedPartition V k d)).probability Good)
    (i : Fin (ℓ + 2)) (v : V) :
    (q * ((m : ℝ) / Fintype.card V - δ) / ρ ≤
      (∑ t, if (t i).1 = v then averagedWeight (FiniteLaw.uniform (FixedPartition V k d))
        (maskWeight Good w) ρ t else 0) ∧
      (∑ t, if (t i).1 = v then averagedWeight (FiniteLaw.uniform (FixedPartition V k d))
        (maskWeight Good w) ρ t else 0) ≤ q * ((m : ℝ) / Fintype.card V) / ρ) ∧
    (q * ((m : ℝ) / Fintype.card V - δ) / ρ ≤
      (∑ t, if (t i).2 = v then averagedWeight (FiniteLaw.uniform (FixedPartition V k d))
        (maskWeight Good w) ρ t else 0) ∧
      (∑ t, if (t i).2 = v then averagedWeight (FiniteLaw.uniform (FixedPartition V k d))
        (maskWeight Good w) ρ t else 0) ≤ q * ((m : ℝ) / Fintype.card V) / ρ) := by
  have hpos (f : (Fin (ℓ + 2) → V × V) → V) (s : Fin (ℓ + 2) ⊕ Fin (ℓ + 2))
      (hp : ∀ P, Good P → (∑ t, if f t = v then w P t else 0) =
        if P.1 v = a s then q else 0) :
      q * ((m : ℝ) / Fintype.card V - δ) / ρ ≤
          (∑ t, if f t = v then averagedWeight (FiniteLaw.uniform (FixedPartition V k d))
            (maskWeight Good w) ρ t else 0) ∧
        (∑ t, if f t = v then averagedWeight (FiniteLaw.uniform (FixedPartition V k d))
          (maskWeight Good w) ρ t else 0) ≤ q * ((m : ℝ) / Fintype.card V) / ρ := by
    have h := averagedWeight_good_incidence_bounds (FiniteLaw.uniform (FixedPartition V k d))
      (maskWeight Good w) (fun t => f t = v) (fun P => P.1 v = a s) Good ρ δ q q hρ hq hgood
      (by
        intro P
        by_cases hg : Good P
        · simp only [maskWeight, hg, ite_true, and_true, hp P hg]
          constructor <;> split_ifs <;> exact le_rfl
        · simp only [maskWeight, hg, ite_false, and_false, ite_self, Finset.sum_const_zero]
          exact ⟨le_rfl, by split_ifs; exact hq; exact le_rfl⟩)
    simpa only [fixedPartition_one_placement, hm] using h
  exact ⟨hpos (fun t => (t i).1) (Sum.inl i) (fun P hP => (hw P hP).positions i v |>.1),
    hpos (fun t => (t i).2) (Sum.inr i) (fun P hP => (hw P hP).positions i v |>.2)⟩

include hw in
theorem averagedPartition_upper (ρ : ℝ) (hρ : 0 < ρ) (hB : 0 ≤ B)
    (t : Fin (ℓ + 2) → V × V) :
    averagedWeight (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w) ρ t ≤ B / ρ := by
  apply div_le_div_of_nonneg_right _ hρ.le
  have h := finiteLaw_expectation_mono (FiniteLaw.uniform (FixedPartition V k d))
    (fun P => maskWeight Good w P t) (fun _ => B) (by
      intro P
      unfold maskWeight
      split_ifs with hg
      · exact (hw P hg).upper t
      · exact hB)
  simpa only [finiteLaw_expectation_const] using h

end

def pairTupleLabels {I V : Type*} (t : I → V × V) : I ⊕ I → V
  | Sum.inl i => (t i).1
  | Sum.inr i => (t i).2

theorem averagedPartition_lower {V : Type*} [Fintype V] {ℓ k : ℕ} {d : Fin k → ℕ}
    [Nonempty (FixedPartition V k d)]
    (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V)
    (a : (Fin (ℓ + 2) ⊕ Fin (ℓ + 2)) ↪ Fin k)
    (Good : FixedPartition V k d → Prop)
    (w : FixedPartition V k d → (Fin (ℓ + 2) → V × V) → ℝ)
    (p q A B : ℝ)
    (hw : ∀ P, Good P → PartitionTupleWeightConditions G σ P a p q A B (w P))
    (m : ℕ) (hm : ∀ i, d (a i) = m) (hn : 0 < Fintype.card V)
    (ρ δ ε : ℝ) (hρ : 0 < ρ) (hA : 0 ≤ A) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hgood : 1-δ ≤ (FiniteLaw.uniform (FixedPartition V k d)).probability Good)
    (hscale : δ ≤ ε * ((m : ℝ) / Fintype.card V) ^ (2 * (ℓ + 2)))
    (t : Fin (ℓ + 2) → V × V) (ht : TwistedCyclicTupleValid G σ t)
    (hinj : Function.Injective (pairTupleLabels t)) :
    A * (1-ε) * ((m : ℝ) / Fintype.card V) ^ (2 * (ℓ + 2)) / ρ ≤
      averagedWeight (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w) ρ t := by
  let μ := FiniteLaw.uniform (FixedPartition V k d)
  let E (P : FixedPartition V k d) := ∀ s, P.1 (pairTupleLabels t s) = a s
  let x : (Fin (ℓ + 2) ⊕ Fin (ℓ + 2)) ↪ V := ⟨pairTupleLabels t, hinj⟩
  have hp := fixedPartition_joint_placement_lower x a m hm hn
  have hj := fixedPartition_good_joint_placement x a m hm hn Good δ ε hε hgood
    (by simpa only [Fintype.card_sum, Fintype.card_fin, ← two_mul] using hscale)
  simp only [Fintype.card_sum, Fintype.card_fin, ← two_mul] at hp
  have hprob : (1-ε) * ((m : ℝ) / Fintype.card V) ^ (2 * (ℓ + 2)) ≤
      μ.probability (fun P => E P ∧ Good P) :=
    (mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hε1)).trans hj
  have he := finiteLaw_expectation_mono μ
    (fun P => if E P ∧ Good P then A else 0) (fun P => maskWeight Good w P t) (by
      intro P
      by_cases hg : Good P
      · simp only [maskWeight, hg, ite_true, and_true]
        split_ifs with hE
        · exact (hw P hg).lower t ht (fun i => ⟨hE (Sum.inl i),hE (Sum.inr i)⟩)
        · exact (hw P hg).nonneg t
      · simp only [maskWeight, hg, ite_false, and_false, le_refl])
  rw [finiteLaw_expectation_indicator_value μ (fun P => E P ∧ Good P) A] at he
  apply div_le_div_of_nonneg_right _ hρ.le
  have hh := mul_le_mul_of_nonneg_left hprob hA
  exact (show A * (1-ε) * ((m : ℝ) / Fintype.card V) ^ (2 * (ℓ + 2)) ≤
    A * μ.probability (fun P => E P ∧ Good P) by simpa only [mul_assoc] using hh).trans he

end Oberwolfach
