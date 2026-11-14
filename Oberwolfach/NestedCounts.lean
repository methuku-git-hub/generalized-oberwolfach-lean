module

public import Oberwolfach.NormalizedSubsetCounts

@[expose] public section

/-! External roots remain in every earlier test domain of a nested sequence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finset_chain_subset {V : Type*} (B : ℕ → Finset V) (k : ℕ)
    (hstep : ∀ i < k, B (i + 1) ⊆ B i)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ k) : B b ⊆ B a := by
  revert hb
  induction b, hab using Nat.le_induction with
  | base => exact fun _ => Finset.Subset.refl _
  | succ b hab ih =>
    intro hb
    exact (hstep b (by omega)).trans (ih (by omega))

theorem abs_chain_difference_bound (f e : ℕ → ℝ) (k : ℕ)
    (hstep : ∀ i < k, |f (i + 1) - f i| ≤ e i) :
    |f k - f 0| ≤ ∑ i ∈ Finset.range k, e i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := ih (fun i hi => hstep i (by omega))
    have hs := hstep k (by omega)
    rw [Finset.sum_range_succ]
    have ht : |f (k + 1) - f 0| ≤ |f (k + 1) - f k| + |f k - f 0| :=
      abs_sub_le _ _ _
    linarith

theorem nested_normalized_count_estimate {V : Type*} (B : ℕ → Finset V)
    (A : V → Finset V) (e : ℕ → ℝ) (k : ℕ)
    (hsub : ∀ i < k, B (i + 1) ⊆ B i)
    (hstep : ∀ i < k, ∀ x ∈ B (i - 1),
      |((A x ∩ B (i + 1)).card : ℝ) / (B (i + 1)).card -
        ((A x ∩ B i).card : ℝ) / (B i).card| ≤ e i)
    {i : ℕ} (hi : i ≤ k) {x : V} (hx : x ∈ B (i - 2)) :
    |((A x ∩ B i).card : ℝ) / (B i).card -
        ((A x ∩ B 0).card : ℝ) / (B 0).card| ≤ ∑ j ∈ Finset.range i, e j := by
  apply abs_chain_difference_bound (fun j => ((A x ∩ B j).card : ℝ) / (B j).card) e i
  intro j hj
  apply hstep j (by omega)
  exact finset_chain_subset B k hsub (by omega : j - 1 ≤ i - 2) (by omega) hx

end Oberwolfach
