module

public import Oberwolfach.FibreCycles
public import Oberwolfach.NestedLevels

@[expose] public section

/-! A long-cycle permutation preserving every level of a nested sequence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem nested_shell_permutation {V : Type*} [Fintype V]
    (B : ℕ → Finset V) (t h : ℕ) (hzero : B 0 = Finset.univ)
    (hsub : ∀ i < t, B (i + 1) ⊆ B i)
    (hsizes : ∀ i < t, (B i \ B (i + 1)).Nonempty → h ≤ (B i \ B (i + 1)).card)
    (hlast : h ≤ (B t).card) :
    ∃ π : Equiv.Perm V,
      (∀ i ≤ t, ∀ x, π x ∈ B i ↔ x ∈ B i) ∧
      (∀ x k, nestedLevel B t ((π ^ k) x) = nestedLevel B t x) ∧
      (∀ x k, 0 < k → k < h → (π ^ k) x ≠ x) := by
  classical
  obtain ⟨π, hπ, hperiod⟩ := fibre_cycles (nestedLevel B t)
  refine ⟨π, ?_, ?_, ?_⟩
  · intro i hi x
    rw [mem_nested_iff_le_level B t hzero hsub (π x) hi,
      mem_nested_iff_le_level B t hzero hsub x hi, hπ x]
  · intro x k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hπ, ih]
  · intro x k hk hkh heq
    have hdiv := (hperiod x k).mp heq
    have hfibre : h ≤ (Finset.univ.filter
        (fun y => nestedLevel B t y = nestedLevel B t x)).card := by
      by_cases ht : nestedLevel B t x = t
      · rw [ht, nestedLevel_fibre_last B t hzero hsub]
        exact hlast
      · have hi : nestedLevel B t x < t := lt_of_le_of_ne (nestedLevel_le B t x) ht
        rw [nestedLevel_fibre_shell B t hzero hsub hi]
        apply hsizes _ hi
        rw [← nestedLevel_fibre_shell B t hzero hsub hi]
        exact ⟨x, by simp⟩
    have hle := Nat.le_of_dvd hk hdiv
    exact (not_lt_of_ge (hfibre.trans hle)) hkh

/-- The no-short-return conclusion makes every interval of length at most h
injectively indexed by its exponent. -/
theorem permutation_short_interval_injective {V : Type*} (π : Equiv.Perm V)
    (h : ℕ) (hnoshort : ∀ x k, 0 < k → k < h → (π ^ k) x ≠ x) (x : V) :
    Function.Injective (fun i : Fin h => (π ^ i.val) x) := by
  have haux (i j : Fin h) (hijlt : i.val < j.val) : (π ^ i.val) x ≠ (π ^ j.val) x := by
    intro hij
    have hreturn : (π ^ (j.val - i.val)) x = x := by
      apply (π ^ i.val).injective
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hijlt.le]
      exact hij.symm
    exact hnoshort x (j.val - i.val) (by omega) (by omega) hreturn
  intro i j hij
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact haux i j hlt hij
  · exact haux j i hgt hij.symm

end Oberwolfach
