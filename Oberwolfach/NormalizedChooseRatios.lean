module

public import Oberwolfach.ChooseRatioLower
public import Oberwolfach.NormalizedProductRatios

@[expose] public section

/-! Exact rescaled inclusion probabilities after removing specified
labels. The finite error records the sample and population corrections
separately, so their order of choice is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem normalized_choose_ratio_product (a t k b d : ℝ) (ha : 0 < a) (ht : 0 < t) (hk : 0 < k)
    (m n r : ℕ) (hm : (m:ℝ)=a*t-b) (hn : (n:ℝ)=a*k-d) (hrm : r ≤ m) (hrn : r ≤ n) :
    (k/t)^r*((m.choose r:ℝ)/n.choose r)=
      ∏ j : Fin r,(1-(b+j.val)/(a*t))/(1-(d+j.val)/(a*k)) := by
  have hp : (m.choose r:ℝ)/n.choose r=∏ j : Fin r,((m-j.val:ℕ):ℝ)/(n-j.val:ℕ) := by
    rw [choose_ratio_product]
    exact (Fin.prod_univ_eq_prod_range (fun j => ((m-j:ℕ):ℝ)/(n-j:ℕ)) r).symm
  calc
    _ = ∏ j : Fin r,(k/t)*(((m-j.val:ℕ):ℝ)/(n-j.val:ℕ)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,hp]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      have hjm : j.val ≤ m := by omega
      have hjn : j.val < n := by omega
      have hjnR : (j.val:ℝ)<n := by exact_mod_cast hjn
      have hden : 0 < a*k-d-j.val := by linarith [hn]
      have hratio : (d+j.val)/(a*k)<1 := (div_lt_one (mul_pos ha hk)).mpr (by linarith)
      have hne : 1-(d+j.val)/(a*k)≠0 := by linarith
      rw [Nat.cast_sub hjm,Nat.cast_sub hjn.le,hm,hn]
      field_simp [ha.ne',ht.ne',hk.ne',hden.ne',hne]
      <;> ring

theorem normalized_profile_inclusion_error {I : Type*} [Fintype I]
    (a b d : I → ℝ) (ha : ∀ i,0 < a i) (hb : ∀ i,0 ≤ b i) (hd : ∀ i,0 ≤ d i)
    (t k : ℝ) (ht : 0 < t) (hk : 0 < k) (m n r : I → ℕ)
    (hm : ∀ i,(m i:ℝ)=a i*t-b i) (hn : ∀ i,(n i:ℝ)=a i*k-d i)
    (hrm : ∀ i,r i ≤ m i) (hrn : ∀ i,r i ≤ n i)
    (hsmall : (∑ j : Σ i,Fin (r i),(d j.1+j.2.val)/(a j.1*k)) ≤ 1/2) :
    |(k/t)^(∑ i,r i)*(∏ i,((m i).choose (r i):ℝ)/(n i).choose (r i))-1| ≤
      2*((∑ j : Σ i,Fin (r i),(b j.1+j.2.val)/(a j.1*t))+
        (∑ j : Σ i,Fin (r i),(d j.1+j.2.val)/(a j.1*k))) := by
  let x := fun j : Σ i,Fin (r i) => (b j.1+j.2.val)/(a j.1*t)
  let y := fun j : Σ i,Fin (r i) => (d j.1+j.2.val)/(a j.1*k)
  have hx (j : Σ i,Fin (r i)) : 0 ≤ x j ∧ x j ≤ 1 := by
    refine ⟨div_nonneg (add_nonneg (hb j.1) (Nat.cast_nonneg _)) (mul_pos (ha _) ht).le,?_⟩
    apply (div_le_one (mul_pos (ha _) ht)).mpr
    have hj : (j.2.val:ℝ) ≤ m j.1 := by exact_mod_cast (show j.2.val ≤ m j.1 by have hh:=hrm j.1;omega)
    linarith [hm j.1]
  have hy (j : Σ i,Fin (r i)) : 0 ≤ y j ∧ y j ≤ 1 := by
    refine ⟨div_nonneg (add_nonneg (hd j.1) (Nat.cast_nonneg _)) (mul_pos (ha _) hk).le,?_⟩
    apply (div_le_one (mul_pos (ha _) hk)).mpr
    have hj : (j.2.val:ℝ) ≤ n j.1 := by exact_mod_cast (show j.2.val ≤ n j.1 by have hh:=hrn j.1;omega)
    linarith [hn j.1]
  have he : (k/t)^(∑ i,r i)*(∏ i,((m i).choose (r i):ℝ)/(n i).choose (r i))=
      (∏ j : Σ i,Fin (r i),(1-x j))/(∏ j : Σ i,Fin (r i),(1-y j)) := by
    rw [← Finset.prod_pow_eq_pow_sum,← Finset.prod_mul_distrib,← Finset.prod_div_distrib,Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    exact normalized_choose_ratio_product (a i) t k (b i) (d i) (ha i) ht hk
      (m i) (n i) (r i) (hm i) (hn i) (hrm i) (hrn i)
  rw [he]
  exact normalized_product_ratio_error Finset.univ x y (fun j _ => hx j) (fun j _ => hy j) hsmall

end Oberwolfach
