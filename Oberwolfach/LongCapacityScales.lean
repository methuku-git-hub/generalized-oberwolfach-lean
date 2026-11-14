module

public import Oberwolfach.CapacityPathProducts
public import Oberwolfach.BalancedCapacityTransitions

@[expose] public section

/-! Explicit powers of the common class size in the long-capacity construction. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem capacity_mass_bounds {X : Type*} [Fintype X]
    (d : X → ℝ) (n M d₀ d₁ : ℝ) (hn : (Fintype.card X : ℝ)=n)
    (hm : ∑ x, d x=M) (hd : ∀ x, d₀*n ≤ d x ∧ d x ≤ d₁*n) :
    d₀*n^2 ≤ M ∧ M ≤ d₁*n^2 := by
  have hlo := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => (hd x).1)
  have hup := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => (hd x).2)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hn,hm] at hlo hup
  constructor <;> nlinarith

theorem capacity_profile_scale {X : Type*} [Fintype X]
    (d : X → ℝ) (n M d₀ d₁ : ℝ) (hn : (Fintype.card X : ℝ)=n)
    (hnpos : 0 < n) (hd₀ : 0 < d₀) (hd₁ : 0 < d₁)
    (hm : ∑ x, d x=M) (hd : ∀ x, d₀*n ≤ d x ∧ d x ≤ d₁*n) (x : X) :
    (d₀/d₁)/n ≤ d x/M ∧ d x/M ≤ (d₁/d₀)/n := by
  obtain ⟨hMlo,hMup⟩ := capacity_mass_bounds d n M d₀ d₁ hn hm hd
  have hM : 0 < M := (mul_pos hd₀ (sq_pos_of_pos hnpos)).trans_le hMlo
  have hlo := div_le_div₀ ((mul_pos hd₀ hnpos).le.trans (hd x).1) (hd x).1 hM hMup
  have hup := div_le_div₀ (mul_pos hd₁ hnpos).le (hd x).2
    (mul_pos hd₀ (sq_pos_of_pos hnpos)) hMlo
  constructor
  · convert hlo using 1; field_simp [hd₁.ne',hnpos.ne']
  · convert hup using 1; field_simp [hd₀.ne',hnpos.ne']

theorem path_probability_bounds {X : Type*}
    (R : ℕ → X → X → ℝ) (i k : ℕ) (p : Fin (k+1) → X)
    (a b : ℝ) (ha : 0 ≤ a)
    (hR : ∀ j : Fin k, a ≤ R (i+j.val) (p j.castSucc) (p j.succ) ∧
      R (i+j.val) (p j.castSucc) (p j.succ) ≤ b) :
    a^k ≤ transitionPathWeight R i k p ∧ transitionPathWeight R i k p ≤ b^k := by
  rw [transitionPathWeight_product]
  constructor
  · simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ => ha) (fun j _ => (hR j).1)
  · simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ => ha.trans (hR j).1) (fun j _ => (hR j).2)

theorem normalized_path_scale (a b c n : ℝ) (hn : 0 < n) (k : ℕ) (hk : 0 < k) :
    (a/(b*n))^k/(c/n)=((a/b)^k/c)/n^(k-1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp only [Nat.add_sub_cancel,Nat.succ_eq_add_one,div_pow,mul_pow,pow_succ]
  field_simp [hn.ne']

theorem degree_times_path_scale (a b d n : ℝ) (hn : 0 < n) (k : ℕ) (hk : 0 < k) :
    (d*n)*(a/(b*n))^k=(d*(a/b)^k)/n^(k-1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp only [Nat.add_sub_cancel,Nat.succ_eq_add_one,div_pow,mul_pow,pow_succ]
  field_simp [hn.ne']

end Oberwolfach
