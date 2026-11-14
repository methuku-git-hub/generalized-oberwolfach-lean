module

public import Oberwolfach.RelatedSelections
public import Oberwolfach.PermutationClose

@[expose] public section

/-! Counting tuples with a close pair after separated coordinates have
been prescribed. Every such pair involves a free coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000 in
theorem bad_fixed_selections_card {I X : Type*}
    [Fintype I] [Fintype X] [DecidableEq I] [Nonempty X]
    (R : X → X → Prop) (hR : ∀ x y, R x y → R y x)
    (q : ℕ) (hdegree : ∀ x, Fintype.card {y // R x y} ≤ q)
    (A : Finset I) (a : I → X)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ R (a i) (a j)) :
    Fintype.card {f : I → X // (∀ i ∈ A, f i = a i) ∧
      ∃ i j, i ≠ j ∧ R (f i) (f j)} ≤
      Fintype.card I ^ 2 * q * Fintype.card X ^ (Fintype.card I - A.card - 1) := by
  let C (p : I × I) := Finset.univ.filter (fun f : I → X =>
    (∀ i ∈ A, f i = a i) ∧ p.1 ∉ A ∧ p.1 ≠ p.2 ∧ R (f p.2) (f p.1))
  have hsub : Finset.univ.filter (fun f : I → X =>
      (∀ i ∈ A, f i = a i) ∧ ∃ i j, i ≠ j ∧ R (f i) (f j)) ⊆
      Finset.univ.biUnion C := by
    intro f hf
    obtain ⟨hf, i, j, hij, hrel⟩ := (Finset.mem_filter.mp hf).2
    by_cases hi : i ∈ A
    · have hj : j ∉ A := by
        intro hj
        apply hsep i hi j hj hij
        simpa only [hf i hi, hf j hj] using hrel
      exact Finset.mem_biUnion.mpr ⟨(j, i), Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, hj, hij.symm, hrel⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, hi, hij, hR _ _ hrel⟩⟩
  have hC (p : I × I) : (C p).card ≤
      q * Fintype.card X ^ (Fintype.card I - A.card - 1) := by
    by_cases hi : p.1 ∈ A
    · simp [C, hi]
    by_cases hij : p.1 = p.2
    · simp [C, hij]
    have heq : (C p).card = Fintype.card {f : I → X //
        (∀ i ∈ A, f i = a i) ∧ R (f p.2) (f p.1)} := by
      simp only [C, ne_eq, hi, hij, not_false_eq_true, true_and, and_true, Fintype.card_subtype]
    rw [heq]
    exact related_fixed_selections_card R q hdegree A a p.1 p.2 hi hij
  calc
    _ ≤ (Finset.univ.biUnion C).card := by
      rw [Fintype.card_subtype]
      exact Finset.card_le_card hsub
    _ ≤ ∑ p : I × I, (C p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : I × I, q * Fintype.card X ^ (Fintype.card I - A.card - 1) :=
      Finset.sum_le_sum (fun p _ => hC p)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_prod, Nat.cast_id]; ring

theorem permutation_close_selections_card {I V : Type*}
    [Fintype I] [Fintype V] [DecidableEq I] [Nonempty V]
    (π : Equiv.Perm V) (b : ℕ) (A : Finset I) (a : I → V)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ PermutationClose π b (a i) (a j)) :
    Fintype.card {f : I → V // (∀ i ∈ A, f i = a i) ∧
      ∃ i j, i ≠ j ∧ PermutationClose π b (f i) (f j)} ≤
      Fintype.card I ^ 2 * (2 * b + 1) *
        Fintype.card V ^ (Fintype.card I - A.card - 1) :=
  bad_fixed_selections_card (PermutationClose π b)
    (fun x y h => (permutationClose_symm π b x y).mp h) (2 * b + 1)
    (permutationClose_neighbour_card π b) A a hsep

end Oberwolfach
