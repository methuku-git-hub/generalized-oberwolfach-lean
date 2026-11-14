module

public import Oberwolfach.NormalizedChooseRatios

@[expose] public section

/-! The finite falling-factorial comparison with separate sample and
population errors. It allows a real ambient scale and integer class
sizes, as in the bounded-extension statement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem profile_correction_sum_bound {I : Type*} [Fintype I]
    (a b : I → ℝ) (ha : ∀ i,1 ≤ a i) (hb : ∀ i,0 ≤ b i)
    (r : I → ℕ) (H : ℕ) (hH : ∑ i,r i=H)
    (P t : ℝ) (hP : 0 ≤ P) (hPt : ∀ i,b i ≤ P) (ht : 0 < t) :
    (∑ j : Σ i,Fin (r i),(b j.1+j.2.val)/(a j.1*t)) ≤ (H:ℝ)*(P+H)/t := by
  have hr (i : I) : r i ≤ H := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=r)
      (fun j _ => Nat.zero_le (r j)) (Finset.mem_univ i)
    simpa only [hH] using hh
  have hcard : Fintype.card (Σ i,Fin (r i))=H := by simp only [Fintype.card_sigma,Fintype.card_fin,hH]
  calc
    _ ≤ ∑ _j : Σ i,Fin (r i),(P+H)/t := by
      apply Finset.sum_le_sum
      intro j _
      have haj : 0 < a j.1 := lt_of_lt_of_le (by norm_num) (ha j.1)
      have hj : (j.2.val:ℝ) ≤ H := by exact_mod_cast (show j.2.val ≤ H by have hh:=hr j.1;omega)
      calc
        _ ≤ (P+H)/(a j.1*t) := div_le_div_of_nonneg_right (by linarith [hPt j.1]) (mul_pos haj ht).le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) ht (by nlinarith [ha j.1])
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul,mul_div_assoc]

theorem normalized_profile_inclusion_error_uniform {I : Type*} [Fintype I]
    (a b d : I → ℝ) (ha : ∀ i,1 ≤ a i) (hb : ∀ i,0 ≤ b i) (hd : ∀ i,0 ≤ d i)
    (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hbP : ∀ i,b i ≤ P) (hdQ : ∀ i,d i ≤ Q)
    (t k : ℝ) (ht : 0 < t) (hk : 0 < k) (m n r : I → ℕ) (H : ℕ) (hH : ∑ i,r i=H)
    (hm : ∀ i,(m i:ℝ)=a i*t-b i) (hn : ∀ i,(n i:ℝ)=a i*k-d i)
    (hrm : ∀ i,r i ≤ m i) (hrn : ∀ i,r i ≤ n i)
    (hlarge : 2*(H:ℝ)*(Q+H) ≤ k) :
    |(k/t)^H*(∏ i,((m i).choose (r i):ℝ)/(n i).choose (r i))-1| ≤
      2*(H:ℝ)*((P+H)/t+(Q+H)/k) := by
  have hx := profile_correction_sum_bound a b ha hb r H hH P t hP hbP ht
  have hy := profile_correction_sum_bound a d ha hd r H hH Q k hQ hdQ hk
  have hsmall : (∑ j : Σ i,Fin (r i),(d j.1+j.2.val)/(a j.1*k)) ≤ 1/2 := by
    apply hy.trans
    apply (div_le_iff₀ hk).mpr
    nlinarith
  have hh := normalized_profile_inclusion_error a b d
    (fun i => lt_of_lt_of_le (by norm_num) (ha i)) hb hd t k ht hk m n r hm hn hrm hrn hsmall
  rw [hH] at hh
  apply hh.trans
  calc
    _ ≤ 2*((H:ℝ)*(P+H)/t+(H:ℝ)*(Q+H)/k) := by linarith
    _ = _ := by ring

end Oberwolfach
