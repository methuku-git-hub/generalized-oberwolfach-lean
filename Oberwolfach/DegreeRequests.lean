module

public import Mathlib.Tactic

@[expose] public section

/-! Finite lists of endpoint requests for exact degree corrections. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem indexPrescribedCounts
    {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℕ) (m : ℕ) (hm : ∑ v, f v = m) :
    ∃ x : Fin m → V, ∀ v, (Finset.univ.filter (fun i => x i = v)).card = f v := by
  classical
  let A := Σ v, Fin (f v)
  have hcard : Fintype.card A = m := by simpa [A, Fintype.card_sigma] using hm
  let σ : Fin m ≃ A := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (σ i).1, ?_⟩
  intro v
  rw [Finset.card_filter, ← σ.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  change (∑ u : (Σ w, Fin (f w)), if u.1 = v then 1 else 0) = f v
  rw [Fintype.sum_sigma]
  have hh (w : V) : (∑ _ : Fin (f w), if w = v then 1 else 0) =
      if w = v then f w else 0 := by
    by_cases hw : w = v <;> simp [hw]
  simp_rw [hh]
  simp

/-- Positive and negative discrepancies give lists of equal length.
The two endpoint classes are disjoint, and their combined use at a vertex
is bounded by its original absolute discrepancy. -/
theorem degreeDiscrepancy_requests
    {V : Type*} [Fintype V] [DecidableEq V]
    (d t : V → ℕ) (htotal : ∑ v, d v = ∑ v, t v)
    {a : ℝ} (_ha : 0 ≤ a)
    (herr : ∀ v, |(d v : ℝ) - t v| ≤ a) :
    ∃ m : ℕ, ∃ x y : Fin m → V,
      ((m : ℝ) ≤ Fintype.card V * a) ∧
      (∀ v, (Finset.univ.filter (fun i => x i = v)).card = d v - t v) ∧
      (∀ v, (Finset.univ.filter (fun i => y i = v)).card = t v - d v) ∧
      (∀ v, ((Finset.univ.filter (fun i => x i = v)).card : ℝ) +
        ((Finset.univ.filter (fun i => y i = v)).card : ℝ) ≤ a) ∧
      ∀ i j, x i ≠ y j := by
  classical
  let p (v : V) := d v - t v
  let q (v : V) := t v - d v
  have hpoint (v : V) : d v + q v = t v + p v := by dsimp [p, q]; omega
  have hequal : ∑ v, p v = ∑ v, q v := by
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun v _ => hpoint v)
    simp only [Finset.sum_add_distrib, htotal] at hh
    omega
  let m := ∑ v, p v
  obtain ⟨x, hx⟩ := indexPrescribedCounts p m rfl
  obtain ⟨y, hy⟩ := indexPrescribedCounts q m hequal.symm
  have hbound (v : V) : (p v : ℝ) + (q v : ℝ) ≤ a := by
    by_cases hd : t v ≤ d v
    · have hq : q v = 0 := Nat.sub_eq_zero_of_le hd
      simp only [p, Nat.cast_sub hd, hq, Nat.cast_zero, add_zero]
      exact (le_abs_self _).trans (herr v)
    · have hp : p v = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hd)
      have htd : d v ≤ t v := le_of_lt (lt_of_not_ge hd)
      simp only [q, Nat.cast_sub htd, hp, Nat.cast_zero, zero_add]
      have hh := (neg_le_abs ((d v : ℝ) - t v)).trans (herr v)
      linarith
  have hsize : (m : ℝ) ≤ Fintype.card V * a := by
    calc
      (m : ℝ) = ∑ v, (p v : ℝ) := by simp [m]
      _ ≤ ∑ _ : V, a := Finset.sum_le_sum (fun v _ => by
        have hp : (0 : ℝ) ≤ q v := Nat.cast_nonneg (q v)
        linarith [hbound v])
      _ = _ := by simp
  refine ⟨m, x, y, hsize, hx, hy, ?_, ?_⟩
  · intro v
    rw [hx, hy]
    exact hbound v
  · intro i j hij
    have hxp : 0 < p (x i) := by
      rw [← hx]
      exact Finset.card_pos.mpr ⟨i, by simp⟩
    have hyq : 0 < q (y j) := by
      rw [← hy]
      exact Finset.card_pos.mpr ⟨j, by simp⟩
    rw [← hij] at hyq
    dsimp [p] at hxp
    dsimp [q] at hyq
    omega

end Oberwolfach
