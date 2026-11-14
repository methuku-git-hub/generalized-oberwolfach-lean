module

public import Oberwolfach.DiscardedTupleWeights
public import Oberwolfach.TwistedTupleEdges
public import Oberwolfach.AveragedPartitionWeights

@[expose] public section

/-! Removing tuples with two close labels. Fixed-coordinate incidence
sums lose exactly the discarded weight; individual weights on retained
tuples are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def separatedWeight {I V : Type*} (π : Equiv.Perm V) (b : ℕ)
    (w : (I → V) → ℝ) (f : I → V) : ℝ :=
  if PermutationSeparated π b f then w f else 0

theorem not_permutationSeparated_iff {I V : Type*} (π : Equiv.Perm V) (b : ℕ) (f : I → V) :
    ¬ PermutationSeparated π b f ↔ ∃ i j, i ≠ j ∧ PermutationClose π b (f i) (f j) := by
  simp only [PermutationSeparated, not_forall, not_imp, not_not, exists_prop]

theorem separatedWeight_retained {I V : Type*} (π : Equiv.Perm V) (b : ℕ)
    (w : (I → V) → ℝ) (f : I → V) (hf : PermutationSeparated π b f) :
    separatedWeight π b w f = w f := by simp only [separatedWeight, hf, ite_true]

theorem separatedWeight_bounds {I V : Type*} (π : Equiv.Perm V) (b : ℕ)
    (w : (I → V) → ℝ) (hw : ∀ f, 0 ≤ w f) (f : I → V) :
    0 ≤ separatedWeight π b w f ∧ separatedWeight π b w f ≤ w f := by
  unfold separatedWeight
  split_ifs
  · exact ⟨hw f,le_rfl⟩
  · exact ⟨le_rfl,hw f⟩

theorem separatedWeight_fixed_load_bounds {I V : Type*}
    [Fintype I] [Fintype V] [DecidableEq I] [Nonempty V]
    (π : Equiv.Perm V) (b : ℕ) (A : Finset I) (a : I → V)
    (hA : 1 ≤ A.card) (hfree : A.card + 1 ≤ Fintype.card I)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ PermutationClose π b (a i) (a j))
    (w : (I → V) → ℝ) (hw : ∀ f, 0 ≤ w f)
    (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ f, w f ≤ C / (Fintype.card V : ℝ) ^ (Fintype.card I - 2)) :
    (∑ f, if ∀ i ∈ A, f i = a i then w f else 0) -
        (Fintype.card I : ℝ) ^ 2 * (2*b+1) * C / (Fintype.card V : ℝ) ^ (A.card-1) ≤
      (∑ f, if ∀ i ∈ A, f i = a i then separatedWeight π b w f else 0) ∧
    (∑ f, if ∀ i ∈ A, f i = a i then separatedWeight π b w f else 0) ≤
      (∑ f, if ∀ i ∈ A, f i = a i then w f else 0) := by
  have hloss := permutation_close_weight_loss π b A a hA hfree hsep w C hC hupper
  have he : (∑ f, if ∀ i ∈ A, f i = a i then separatedWeight π b w f else 0) +
      (∑ f, if (∀ i ∈ A, f i = a i) ∧
        (∃ i j, i ≠ j ∧ PermutationClose π b (f i) (f j)) then w f else 0) =
        (∑ f, if ∀ i ∈ A, f i = a i then w f else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro f _
    simp only [← not_permutationSeparated_iff]
    by_cases ha : ∀ i ∈ A, f i = a i <;>
      by_cases hs : PermutationSeparated π b f <;> simp [separatedWeight, ha, hs]
  constructor
  · linarith
  · apply Finset.sum_le_sum
    intro f _
    split_ifs
    · exact (separatedWeight_bounds π b w hw f).2
    · exact le_rfl

theorem separatedWeight_one_position {I V : Type*}
    [Fintype I] [Fintype V] [DecidableEq I] [Nonempty V]
    (π : Equiv.Perm V) (b : ℕ) (hc : 2 ≤ Fintype.card I)
    (i : I) (x : V) (w : (I → V) → ℝ) (hw : ∀ f, 0 ≤ w f)
    (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ f, w f ≤ C / (Fintype.card V : ℝ) ^ (Fintype.card I - 2)) :
    (∑ f, if f i = x then w f else 0) - (Fintype.card I : ℝ)^2*(2*b+1)*C ≤
        (∑ f, if f i = x then separatedWeight π b w f else 0) ∧
      (∑ f, if f i = x then separatedWeight π b w f else 0) ≤
        (∑ f, if f i = x then w f else 0) := by
  have h := separatedWeight_fixed_load_bounds π b {i} (fun _ => x) (by simp)
    (by simpa using hc)
    (by intro j hj k hk hjk; simp only [Finset.mem_singleton] at hj hk; subst j; subst k; exact (hjk rfl).elim)
    w hw C hC hupper
  simpa using h

theorem separatedWeight_two_positions {I V : Type*}
    [Fintype I] [Fintype V] [DecidableEq I] [Nonempty V]
    (π : Equiv.Perm V) (b : ℕ) (hc : 3 ≤ Fintype.card I)
    (i j : I) (hij : i ≠ j) (x y : V) (hxy : ¬ PermutationClose π b x y)
    (w : (I → V) → ℝ) (hw : ∀ f, 0 ≤ w f) (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ f, w f ≤ C / (Fintype.card V : ℝ) ^ (Fintype.card I - 2)) :
    (∑ f, if f i = x ∧ f j = y then w f else 0) -
        (Fintype.card I : ℝ)^2*(2*b+1)*C / Fintype.card V ≤
        (∑ f, if f i = x ∧ f j = y then separatedWeight π b w f else 0) ∧
      (∑ f, if f i = x ∧ f j = y then separatedWeight π b w f else 0) ≤
        (∑ f, if f i = x ∧ f j = y then w f else 0) := by
  let a := Function.update (fun _ : I => y) i x
  have hji : j ≠ i := Ne.symm hij
  have hcard : ({i,j} : Finset I).card = 2 := by simp [hij]
  have hyx : ¬ PermutationClose π b y x := (permutationClose_symm π b y x).not.mpr hxy
  have hsep : ∀ r ∈ ({i,j} : Finset I), ∀ s ∈ ({i,j} : Finset I), r ≠ s →
      ¬ PermutationClose π b (a r) (a s) := by
    intro r hr s hs hrs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr hs
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;>
      simp_all [a,Function.update_apply]
  have h := separatedWeight_fixed_load_bounds π b {i,j} a (by rw [hcard]; omega)
    (by rw [hcard]; exact hc) hsep w hw C hC hupper
  have he (f : I → V) : (∀ r ∈ ({i,j} : Finset I), f r = a r) ↔ f i = x ∧ f j = y := by
    simp [a,Function.update_apply,hij,Ne.symm hij]
  simpa only [he,hcard,show (2:ℕ)-1=1 from rfl,pow_one] using h

def pairTupleLabelsEquiv (I V : Type*) : (I → V × V) ≃ (I ⊕ I → V) where
  toFun := pairTupleLabels
  invFun f i := (f (Sum.inl i),f (Sum.inr i))
  left_inv t := by funext i; rfl
  right_inv f := by funext s; cases s <;> rfl

theorem pairTupleLabels_sum {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V]
    (F : (I ⊕ I → V) → ℝ) :
    (∑ t : I → V × V, F (pairTupleLabels t)) = ∑ f : I ⊕ I → V, F f :=
  Fintype.sum_equiv (pairTupleLabelsEquiv I V) _ _ (fun _ => rfl)

end Oberwolfach
