module

public import Oberwolfach.PairedLabelsFromTuples

@[expose] public section

/-! Quantitative greedy choices for the base cycle and all its common paths.
The finite sum retains every ordered choice; no independence is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

abbrev PairedTupleChoice (x : Fin (m+1) → V)
    (Base : (Fin (m+1) → V) → Prop)
    (Path : (Fin (m+1) → V) → ℕ → (Fin m → V) → Prop) :=
  Σ y : {y // Base y ∧ ∀ i,y i∉Finset.univ.image x},
    {g : Fin (m+1) → Fin m → V //
      DisjointTupleGood (Finset.univ.image x∪Finset.univ.image y.val) (Path y.val) g}

theorem pairedTupleChoice_count (x : Fin (m+1) → V)
    (Base : (Fin (m+1) → V) → Prop)
    (Path : (Fin (m+1) → V) → ℕ → (Fin m → V) → Prop)
    (A M a : ℝ) (ha : 0≤a)
    (hbase : A+(m+1:ℝ)^2*(Fintype.card V:ℝ)^m≤Fintype.card {y // Base y})
    (hcount : ∀ y,Base y → (∀ i,y i∉Finset.univ.image x) → ∀ n<m+1,M≤Fintype.card {g // Path y n g})
    (hinj : ∀ y,Base y → (∀ i,y i∉Finset.univ.image x) → ∀ n<m+1,∀ g,Path y n g → Function.Injective g)
    (hbudget : a+(m:ℝ)*(2*(m+1)+(m+1)*m)*(Fintype.card V:ℝ)^(m-1)≤M) :
    A*a^(m+1)≤Fintype.card (PairedTupleChoice x Base Path) := by
  let Y := {y // Base y ∧ ∀ i,y i∉Finset.univ.image x}
  have hX : ((Finset.univ.image x).card:ℝ)≤m+1 := by
    exact_mod_cast (Finset.card_image_le.trans_eq (Fintype.card_fin (m+1)))
  have hdel := tuple_family_avoiding_lower (m+1) Base (Finset.univ.image x)
  have hloss := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hX (by positivity : (0:ℝ)≤m+1))
    (pow_nonneg (Nat.cast_nonneg (Fintype.card V)) m)
  have hY : A≤(Fintype.card Y:ℝ) := by
    dsimp [Y]
    norm_num only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at hdel
    nlinarith [hdel]
  have hf (y : Y) : a^(m+1)≤Fintype.card
      {g : Fin (m+1) → Fin m → V //
        DisjointTupleGood (Finset.univ.image x∪Finset.univ.image y.val) (Path y.val) g} := by
    apply sequential_disjoint_tuple_count m (m+1) _ (Path y.val) M a ha
      (hcount y.val y.property.1 y.property.2) (hinj y.val y.property.1 y.property.2)
    have hW : ((Finset.univ.image x∪Finset.univ.image y.val).card:ℝ)≤2*(m+1) := by
      have hh := (Finset.card_union_le (Finset.univ.image x) (Finset.univ.image y.val)).trans
        (Nat.add_le_add (Finset.card_image_le.trans_eq (Fintype.card_fin (m+1)))
          (Finset.card_image_le.trans_eq (Fintype.card_fin (m+1))))
      have hh' : ((Finset.univ.image x∪Finset.univ.image y.val).card:ℝ)≤(m+1:ℝ)+(m+1) := by exact_mod_cast hh
      linarith
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add_right hW ((m+1:ℝ)*m)) (Nat.cast_nonneg m))
      (pow_nonneg (Nat.cast_nonneg (Fintype.card V)) (m-1))
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith
  calc
    A*a^(m+1) ≤ (Fintype.card Y:ℝ)*a^(m+1) := mul_le_mul_of_nonneg_right hY (pow_nonneg ha _)
    _ = ∑ _y : Y,a^(m+1) := by simp
    _ ≤ ∑ y : Y,(Fintype.card {g : Fin (m+1) → Fin m → V //
        DisjointTupleGood (Finset.univ.image x∪Finset.univ.image y.val) (Path y.val) g}:ℝ) :=
      Finset.sum_le_sum (fun y _ => hf y)
    _ = Fintype.card (PairedTupleChoice x Base Path) := by
      simp only [PairedTupleChoice,Fintype.card_sigma,Nat.cast_sum]
      congr!

end Oberwolfach
