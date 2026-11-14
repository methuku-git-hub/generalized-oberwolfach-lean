module

public import Oberwolfach.GraphPartitionDegrees

@[expose] public section

/-! A good-partition event on the original graph. Prescribed-tuple events
will be intersected with this same event, using exact placement probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graphCellDegree_intersection {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Equiv.Perm V) (P : FixedPartition V k d) (v : V) (a : Fin k) :
    graphCellDegree G σ P v a =
      ((Finset.univ.filter (fun x => G.Adj v (σ x))) ∩ (fixedPartitionCell P a).1).card := by
  unfold graphCellDegree fixedPartitionCell
  congr 1
  ext x
  simp

theorem graphPartition_degree_tail {V : Type*} [Fintype V] [Nonempty V]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)]
    (G : SimpleGraph V) (σ : Equiv.Perm V) (v : V) (a : Fin k)
    (m : ℕ) (hm : 0 < m) (hsize : d a = m) (D ε η : ℝ)
    (hη : 0 < η) (hε : ε ≤ η / 2)
    (hdeg : |(G.degree v : ℝ) - D| ≤ ε * Fintype.card V) :
    (FiniteLaw.uniform (FixedPartition V k d)).probability
      (fun P => η * m ≤ |(graphCellDegree G σ P v a : ℝ) - D * ((m : ℝ) / Fintype.card V)|) ≤
      2 * Real.exp (-η ^ 2 * m / 2) := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  let A := Finset.univ.filter (fun x => G.Adj v (σ x))
  have hmean := scaled_degree_mean_error hn hm'.le hdeg
  have hmargin := mul_le_mul_of_nonneg_right hε hm'.le
  have htail := fixedPartition_cell_count_tail (d := d) a A
    (show 0 ≤ η * m / 2 by positivity)
  have hsizeR : (d a : ℝ) = m := by exact_mod_cast hsize
  rw [hsizeR] at htail
  have hexp : -2 * (η * m / 2) ^ 2 / (m : ℝ) = -η ^ 2 * m / 2 := by field_simp
  rw [hexp] at htail
  apply le_trans (finiteLaw_probability_mono _ _ _ ?_) htail
  intro P hP
  rw [graphCellDegree_intersection] at hP
  have hcount : A.card = G.degree v := permutation_neighbour_count G σ v
  rw [hcount]
  have htri := abs_sub_le ((A ∩ (fixedPartitionCell P a).1).card : ℝ)
    ((G.degree v : ℝ) * ((m : ℝ) / Fintype.card V))
    (D * ((m : ℝ) / Fintype.card V))
  change η * m ≤ |((A ∩ (fixedPartitionCell P a).1).card : ℝ) -
    D * ((m : ℝ) / Fintype.card V)| at hP
  linarith

theorem graphPartition_common_good {V J : Type*} [Fintype V] [Nonempty V] [Fintype J]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)]
    (G : SimpleGraph V) (σ : J → Equiv.Perm V) (classes : Finset (Fin k))
    (m : ℕ) (hm : 0 < m) (hsize : ∀ a ∈ classes, d a = m) (D ε η : ℝ)
    (hη : 0 < η) (hε : ε ≤ η / 2)
    (hdeg : ∀ v, |(G.degree v : ℝ) - D| ≤ ε * Fintype.card V) :
    1 - (classes.card : ℝ) * Fintype.card J * Fintype.card V *
        (2 * Real.exp (-η ^ 2 * m / 2)) ≤
    (FiniteLaw.uniform (FixedPartition V k d)).probability
      (fun P => ∀ a ∈ classes, ∀ j v,
        |(graphCellDegree G (σ j) P v a : ℝ) - D * ((m : ℝ) / Fintype.card V)| < η * m) := by
  let tests := classes ×ˢ (Finset.univ : Finset (J × V))
  have h := finiteLaw_common_event_lower (FiniteLaw.uniform (FixedPartition V k d)) tests
    (fun z P => η * m ≤ |(graphCellDegree G (σ z.2.1) P z.2.2 z.1 : ℝ) -
      D * ((m : ℝ) / Fintype.card V)|)
    (fun _ => 2 * Real.exp (-η ^ 2 * m / 2))
    (fun z hz => graphPartition_degree_tail G (σ z.2.1) z.2.2 z.1 m hm
      (hsize _ (Finset.mem_product.mp hz).1) D ε η hη hε (hdeg _))
  simp only [tests, Finset.sum_const, Finset.card_product, Finset.card_univ,
    Fintype.card_prod, Nat.cast_mul, nsmul_eq_mul, Finset.mem_product, Finset.mem_univ,
    and_true, Prod.forall, not_le, mul_assoc] at h
  simp only [mul_assoc]
  apply h.trans_eq
  congr 1
  ext P
  constructor
  · intro hp a ha j v; exact hp a j v ha
  · intro hp a j v ha; exact hp a ha j v

end Oberwolfach
