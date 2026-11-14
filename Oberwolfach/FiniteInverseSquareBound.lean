module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section
/-! A uniform finite inverse-square bound for locally scaled union bounds. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem inverse_square_range_bound : ∀ n:ℕ, 1≤n →
    (∑ k∈Finset.range n, (1:ℝ)/((k:ℝ)+1)^2) ≤ 2-1/(n:ℝ) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n=0
    · subst n
      norm_num
    · have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
      have hp : (0:ℝ)<(n:ℝ)+1 := by positivity
      have hp2 : (0:ℝ)<((n:ℝ)+1)^2 := sq_pos_of_pos hp
      have hi:=ih (by omega)
      rw [Finset.sum_range_succ]
      push_cast
      have hstep : 1/((n:ℝ)+1)^2 ≤ 1/(n:ℝ)-1/((n:ℝ)+1) := by
        have hdiff : (1:ℝ)/(n:ℝ)-1/((n:ℝ)+1)=1/((n:ℝ)*((n:ℝ)+1)) := by
          field_simp
          <;> ring
        rw [hdiff]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      linarith

theorem inverse_square_finset_bound (T:Finset ℕ) :
    (∑ k∈T, (1:ℝ)/((k:ℝ)+1)^2) ≤ 2 := by
  have hsub:T⊆Finset.range (T.sup id+1):=by
    intro x hx
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f:=id) hx)
  have h:=Finset.sum_le_sum_of_subset_of_nonneg hsub (by
    intro i hi hi'
    positivity : ∀ i∈Finset.range (T.sup id+1),i∉T→0≤(1:ℝ)/((i:ℝ)+1)^2)
  have hr:=inverse_square_range_bound (T.sup id+1) (by omega)
  have hs:(0:ℝ)≤1/((T.sup id+1:ℕ):ℝ):=by positivity
  linarith
end Oberwolfach
