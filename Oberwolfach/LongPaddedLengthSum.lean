module

public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! A uniform bound on the total length of the fixed padded index list. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_padded_length_sum_bound (K:ℕ):
    (∑i:Fin K,((longPaddedSeedExponent i+2:ℕ):ℝ))≤(K:ℝ)*(max 3 K:ℕ) :=by
  calc
    _ ≤ ∑_i:Fin K,((max 3 K:ℕ):ℝ) :=by
      apply Finset.sum_le_sum
      intro i hi
      have h:longPaddedSeedExponent i+2≤max 3 K:=by
        rw [long_padded_seed_length_eq_exponent]
        unfold longAssignedPaddedLength
        exact max_le_max le_rfl (Nat.succ_le_of_lt i.isLt)
      exact_mod_cast h
    _ = (K:ℝ)*(max 3 K:ℕ) :=by simp

theorem long_padded_length_error_bound (K n:ℕ) (eps:ℝ):
    ((max eps 0)*(n:ℝ))*(∑i:Fin K,((longPaddedSeedExponent i+2:ℕ):ℝ)) ≤
      ((max eps 0)*(n:ℝ))*((K:ℝ)*(max 3 K:ℕ)) :=by
  exact mul_le_mul_of_nonneg_left (long_padded_length_sum_bound K) (by positivity)

theorem long_padded_error_parameter (K:ℕ) (δ:ℝ) (hδ:0<δ):
    ∃eps:ℝ,0<eps ∧ ∀n:ℕ,
      (eps*(n:ℝ))*(∑i:Fin K,((longPaddedSeedExponent i+2:ℕ):ℝ))≤δ*n :=by
  let C:ℝ:=(K:ℝ)*(max 3 K:ℕ)
  have hC:0≤C:=by positivity
  have hden:0<C+1:=by linarith
  refine ⟨δ/(C+1),div_pos hδ hden,?_⟩
  intro n
  have hscale:0≤(δ/(C+1))*(n:ℝ):=by positivity
  have hs:=mul_le_mul_of_nonneg_left (long_padded_length_sum_bound K) hscale
  have hr:δ/(C+1)*C≤δ:=by
    have ha:C≤C+1:=by linarith
    have hb:δ/(C+1)*C≤δ/(C+1)*(C+1):=mul_le_mul_of_nonneg_left ha (le_of_lt (div_pos hδ hden))
    simpa [ne_of_gt hden] using hb
  have hn:0≤(n:ℝ):=by positivity
  calc
    _ ≤ (δ/(C+1)*(n:ℝ))*C:=hs
    _ = (δ/(C+1)*C)*(n:ℝ):=by ring
    _ ≤ δ*n:=mul_le_mul_of_nonneg_right hr hn

theorem long_padded_error_parameter_with_ceiling (K:ℕ) (δ κ:ℝ) (hδ:0<δ) (hκ:0<κ):
    ∃eps:ℝ,0<eps ∧ eps≤κ ∧ ∀n:ℕ,
      (eps*(n:ℝ))*(∑i:Fin K,((longPaddedSeedExponent i+2:ℕ):ℝ))≤δ*n :=by
  obtain ⟨eps₀,heps₀,hbound⟩:=long_padded_error_parameter K δ hδ
  refine ⟨min eps₀ κ,lt_min heps₀ hκ,min_le_right _ _,?_⟩
  intro n
  have hn:0≤(n:ℝ):=by positivity
  have hs:0≤∑i:Fin K,((longPaddedSeedExponent i+2:ℕ):ℝ):=by positivity
  calc
    _ ≤ (eps₀*(n:ℝ))*(∑i:Fin K,((longPaddedSeedExponent i+2:ℕ):ℝ)):=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hn) hs
    _ ≤ δ*n:=hbound n

theorem long_padded_error_parameter_for_assignment (K:ℕ) (hK:0<K) (θ lam δ:ℝ)
    (hθ:0<θ) (hlam:0<lam) (hδ:0<δ):
    ∃eps:ℝ,0<eps ∧ eps≤lam*(θ/(100*(K:ℝ)^2)) ∧ ∀n:ℕ,
      (eps*(n:ℝ))*(∑i:Fin K,((longPaddedSeedExponent i+2:ℕ):ℝ))≤δ*n :=by
  have hKreal:0<(K:ℝ):=by exact_mod_cast hK
  have hcap:0<lam*(θ/(100*(K:ℝ)^2)):=by positivity
  exact long_padded_error_parameter_with_ceiling K δ (lam*(θ/(100*(K:ℝ)^2))) hδ hcap
end Oberwolfach
