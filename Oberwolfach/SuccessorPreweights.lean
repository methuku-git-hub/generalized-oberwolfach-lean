module

public import Oberwolfach.AveragedPartitionWeights
public import Oberwolfach.SuccessorGoodPartitions
public import Oberwolfach.SuccessorAverageEstimates

@[expose] public section

/-! Quantitative assembly of the preliminary successor weights. The
partition law, regularization law, cyclic weights and physical endpoints
are all instantiated here. Only explicit numerical margins remain for
the later asymptotic parameter choice. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure SuccessorPreweightConditions {V : Type*} [Fintype V] {ℓ : ℕ}
    (G : SimpleGraph V) (σ : Fin (ℓ + 2) → Equiv.Perm V)
    (D edgeError vertexError A B : ℝ) (w : (Fin (ℓ + 2) → V × V) → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ w t
  invalid_zero : ∀ t, ¬ TwistedCyclicTupleValid G σ t → w t = 0
  upper : ∀ t, w t ≤ B / (Fintype.card V : ℝ) ^ (2 * ℓ + 2)
  lower : ∀ t, TwistedCyclicTupleValid G σ t → Function.Injective (pairTupleLabels t) →
    A / (Fintype.card V : ℝ) ^ (2 * ℓ + 2) ≤ w t
  left : ∀ i x y, x ≠ y → G.Adj x y →
    1-edgeError ≤ (∑ t, if t i = (x,y) then w t else 0) ∧
      (∑ t, if t i = (x,y) then w t else 0) ≤ 1
  right : ∀ i x y, x ≠ y → G.Adj x (σ i y) →
    1-edgeError ≤ (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y) then w t else 0) ∧
      (∑ t, if ((t i).2,(t (finRotate (ℓ + 2) i)).1) = (x,y) then w t else 0) ≤ 1
  positions : ∀ i v,
    ((1-vertexError) * D ≤ (∑ t, if (t i).1 = v then w t else 0) ∧
      (∑ t, if (t i).1 = v then w t else 0) ≤ D) ∧
    ((1-vertexError) * D ≤ (∑ t, if (t i).2 = v then w t else 0) ∧
      (∑ t, if (t i).2 = v then w t else 0) ≤ D)

theorem successor_preweights_quantitative (β : ℝ) (hβ : 0 < β) :
    ∃ C η₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ m₀ : ℕ, ∀ (V : Type) [Fintype V] [Nonempty V] (ℓ k : ℕ) (d : Fin k → ℕ)
      [Nonempty (FixedPartition V k d)]
      (G : SimpleGraph V) (π : Equiv.Perm V) (b : Fin (ℓ + 2) → Bool)
      (a : (Fin (ℓ + 2) ⊕ Fin (ℓ + 2)) ↪ Fin k) (m : ℕ),
      (∀ s, d (a s) = m) → 0 < m → m₀ ≤ m → 2 ≤ Fintype.card V → m ≤ Fintype.card V →
      ∀ (D ε₀ α ε τ K : ℝ), 0 < α → 0 ≤ ε →
      (Fintype.card V : ℝ) / 2 ≤ D → D ≤ 2 * Fintype.card V →
      ε₀ ≤ η / 2 → (∀ v, |(G.degree v : ℝ) - D| ≤ ε₀ * Fintype.card V) →
      (1/2+β) * m ≤ D * ((m : ℝ) / Fintype.card V) - η * m →
      (Fintype.card V : ℝ) ≤ K * m →
      let q := ⌊D * ((m : ℝ) / Fintype.card V) - Real.sqrt η * m⌋₊
      ((ℓ + 2) + (2 * (ℓ + 2) - 1) * α) * m ≤ (2 * (ℓ + 2) - 1) * (q : ℝ) →
      0 ≤ D * ((m : ℝ) / Fintype.card V) - Real.sqrt η * m →
      C * Real.sqrt η ≤ 1 → 2 * (ℓ + 2 : ℝ) * (C * Real.sqrt η) ≤ 1 / 2 →
      Real.sqrt η + 1 / m + 2 / Fintype.card V + 2 * ε ≤ τ / 2 →
      let δ := 4 * (2 * (ℓ + 2 : ℝ)) * Fintype.card V * Real.exp (-η ^ 2 * m / 2)
      δ ≤ ε * successorPairProbability m (Fintype.card V) →
      δ ≤ (1/2) * ((m : ℝ) / Fintype.card V) ^ (2 * (ℓ + 2)) →
      ∃ w, SuccessorPreweightConditions G (fun i => choosePermutation π (b i)) D
        (C * Real.sqrt η + ε) τ (((ℓ + 2 : ℝ) * cyclicSectorLower ℓ α) / 8)
        (((ℓ + 2 : ℝ) * cyclicSectorUpper ℓ α) * K ^ (2 * (ℓ + 2))) w := by
  obtain ⟨C,η₀,hC,hη₀,hall⟩ := near_regular_partition_tuple_weights β hβ
  refine ⟨C,η₀,hC,hη₀,?_⟩
  intro η hη hηsmall
  obtain ⟨m₀,hm₀⟩ := hall η hη hηsmall
  refine ⟨m₀,?_⟩
  intro V _ _ ℓ k d _ G π b a m hm hmpos hmlarge hn2 hmn D ε₀ α ε τ K hα hε hD hDup hε₀ hdeg hmin hK
    q hthreshold harg hp1 hcp hmargin δ hδ hδtuple
  let σ (i : Fin (ℓ + 2)) := choosePermutation π (b i)
  let Good : FixedPartition V k d → Prop := SuccessorPartitionGood G π a m D η
  let ρ := successorPairProbability m (Fintype.card V)
  let p := C * Real.sqrt η
  let A₀ := (ℓ + 2 : ℝ) * cyclicSectorLower ℓ α
  let B₀ := (ℓ + 2 : ℝ) * cyclicSectorUpper ℓ α
  let A := (1-2*(ℓ+2)*p) * (A₀ / (m : ℝ) ^ (2*ℓ+2))
  let B := B₀ / (m : ℝ) ^ (2*ℓ+2)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn2
  have hρ : 0 < ρ := successorPairProbability_pos hmR (by linarith)
  have hp : 0 ≤ p := mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hA₀ : 0 < A₀ := mul_pos (by positivity) (cyclicSectorConstants_pos ℓ α hα).1
  have hB₀ : 0 < B₀ := mul_pos (by positivity) (cyclicSectorConstants_pos ℓ α hα).2
  have hA : 0 ≤ A := mul_nonneg (by dsimp [p] at *; linarith) (by positivity)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgood : 1-δ ≤ (FiniteLaw.uniform (FixedPartition V k d)).probability Good := by
    have h := successorPartitionGood_probability G π a m hmpos hm D ε₀ η hη hε₀ hdeg
    convert h using 1 <;> simp only [δ,Good,Fintype.card_sum,Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] <;> ring
  have hex : ∀ P : FixedPartition V k d, ∃ w,
      Good P → PartitionTupleWeightConditions G σ P a p q A B w := by
    intro P
    by_cases hg : Good P
    · obtain ⟨hid,hσ⟩ := successorPartitionGood_interface_degrees G π b a m D η P hg
      obtain ⟨w,hw⟩ := hm₀ V ℓ k d G σ P a m hm hmpos hmlarge
        (D * ((m : ℝ) / Fintype.card V)) α hα hmin hid hσ hthreshold
      exact ⟨w,fun _ => hw⟩
    · exact ⟨fun _ => 0,fun h => (hg h).elim⟩
  choose w hw using hex
  let W := averagedWeight (FiniteLaw.uniform (FixedPartition V k d)) (maskWeight Good w) ρ
  have hnon := averagedPartition_nonneg G σ a Good w p q A B hw ρ hρ.le
  have hpos := averagedPartition_positions G σ a Good w p q A B hw m hm δ ρ hρ
    (show (0 : ℝ) ≤ q by positivity) hgood
  have hupper := averagedPartition_upper G σ a Good w p q A B hw ρ hρ hB
  have hlower := averagedPartition_lower G σ a Good w p q A B hw m hm Fintype.card_pos
    ρ δ (1/2) hρ hA (by norm_num) (by norm_num) hgood hδtuple
  have hc : 2 ≤ 2*(ℓ+2) := by omega
  have he : 2*(ℓ+2)-2 = 2*ℓ+2 := by omega
  refine ⟨W,⟨hnon, averagedPartition_invalid_zero G σ a Good w p q A B hw ρ,
    ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro t
    have hh := successor_tuple_normalization_upper hc B₀ (m : ℝ) (Fintype.card V) K
      hB₀.le hmR (by linarith) hK
    rw [he] at hh
    exact (hupper t).trans hh
  · intro t ht hi
    have hh := successor_preliminary_tuple_bounds hc A₀ B₀ p m (Fintype.card V) K (W t)
      hA₀.le hB₀.le hmR hnR hK (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hcp)
      (by simpa only [A,ρ,W,he,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,show (1:ℝ)-1/2=1/2 by norm_num] using hlower t ht hi)
      (by simpa only [he] using hupper t)
    simpa only [he, div_div] using hh.1
  · intro i x y hxy hG
    have h := averagedPartition_left_edge G σ a Good w p q A B hw m hm δ ε hp hp1 hε hρ hgood hδ i x y hxy hG
    exact ⟨by dsimp [W]; linarith [h.1], h.2⟩
  · intro i x y hxy hG
    have h := averagedPartition_right_edge G σ a Good w p q A B hw m hm δ ε hp hp1 hε hρ hgood hδ i x y hxy hG
    exact ⟨by dsimp [W]; linarith [h.1], h.2⟩
  · intro i v
    have hstep (L : ℝ) (hL : (q : ℝ) * ((m : ℝ) / Fintype.card V - δ) / ρ ≤ L ∧
        L ≤ q * ((m : ℝ) / Fintype.card V) / ρ) : (1-τ)*D ≤ L ∧ L ≤ D := by
      apply successor_averaged_position_bounds (by linarith : (1 : ℝ) < Fintype.card V) hmR
        (by exact_mod_cast hmn) hD hDup (Real.sqrt_nonneg _) hε
        (by simpa only [mul_div_assoc] using harg) hδ hmargin
      · simpa only [q,mul_div_assoc] using hL.1
      · simpa only [q,mul_div_assoc] using hL.2
    exact ⟨hstep _ (hpos i v).1,hstep _ (hpos i v).2⟩

end Oberwolfach
