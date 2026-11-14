module

public import Oberwolfach.ThreeIntervalSectorFormula

@[expose] public section

/-! The three interval lengths contribute exactly the exponent c-2. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem fin3_product_erase (f : Fin 3 → ℝ) (c : Fin 3) :
    (∏ i ∈ Finset.univ.erase c, f i)=f (finRotate 3 c)*f (finRotate 3 (finRotate 3 c)) := by
  have he : Finset.univ.erase c={finRotate 3 c,finRotate 3 (finRotate 3 c)} := by
    fin_cases c <;> decide
  rw [he]
  simp

theorem fin3_product_erase_twice (f : Fin 3 → ℝ) (c : Fin 3) :
    (∏ i ∈ (Finset.univ.erase c).erase (finRotate 3 c), f i)=f (finRotate 3 (finRotate 3 c)) := by
  have he : (Finset.univ.erase c).erase (finRotate 3 c)={finRotate 3 (finRotate 3 c)} := by
    fin_cases c <;> decide
  rw [he,Finset.prod_singleton]

theorem fin3_rotated_sum (L : Fin 3 → ℕ) (c : Fin 3) :
    L c+L (finRotate 3 c)+L (finRotate 3 (finRotate 3 c))=∑ i,L i := by
  fin_cases c <;> norm_num [finRotate_apply,Fin.sum_univ_succ] <;> omega

theorem three_path_scale (n a b c d : ℝ) (hn : 0<n)
    (k l m : ℕ) (hk : 0<k) (hl : 0<l) (hm : 0<m) :
    ((a/n^(k-1))*(b/n^(l-1))*(c/n^(m-1)))/(d*n) =
      (a*b*c/d)/n^(k+l+m-2) := by
  have he : k+l+m-2=(k-1)+(l-1)+(m-1)+1 := by omega
  rw [he]
  simp only [pow_add,pow_one]
  field_simp [hn.ne']

theorem three_path_scale_bounds
    (n u v w z a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ) (hn : 0<n)
    (k l m : ℕ) (hk : 0<k) (hl : 0<l) (hm : 0<m)
    (ha₀ : 0<a₀) (hb₀ : 0<b₀) (hc₀ : 0<c₀) (hd₀ : 0<d₀)
    (hu : a₀/n^(k-1) ≤ u ∧ u ≤ a₁/n^(k-1))
    (hv : b₀/n^(l-1) ≤ v ∧ v ≤ b₁/n^(l-1))
    (hw : c₀/n^(m-1) ≤ w ∧ w ≤ c₁/n^(m-1))
    (hz : d₀*n ≤ z ∧ z ≤ d₁*n) :
    (a₀*b₀*c₀/d₁)/n^(k+l+m-2) ≤ u*v*w/z ∧
      u*v*w/z ≤ (a₁*b₁*c₁/d₀)/n^(k+l+m-2) := by
  have hu0 : 0<u := (by positivity : 0<a₀/n^(k-1)).trans_le hu.1
  have hv0 : 0<v := (by positivity : 0<b₀/n^(l-1)).trans_le hv.1
  have hw0 : 0<w := (by positivity : 0<c₀/n^(m-1)).trans_le hw.1
  have hz0 : 0<z := (mul_pos hd₀ hn).trans_le hz.1
  have huv := mul_le_mul hu.1 hv.1 (by positivity) hu0.le
  have huvw := mul_le_mul huv hw.1 (by positivity) (mul_pos hu0 hv0).le
  have huv' := mul_le_mul hu.2 hv.2 hv0.le (hu0.le.trans hu.2)
  have huvw' := mul_le_mul huv' hw.2 hw0.le
    (mul_nonneg (hu0.le.trans hu.2) (hv0.le.trans hv.2))
  have hlo := div_le_div₀ (mul_pos (mul_pos hu0 hv0) hw0).le huvw hz0 hz.2
  have hup := div_le_div₀
    (mul_nonneg (mul_nonneg (hu0.le.trans hu.2) (hv0.le.trans hv.2)) (hw0.le.trans hw.2))
    huvw' (mul_pos hd₀ hn) hz.1
  rw [three_path_scale n a₀ b₀ c₀ d₁ hn k l m hk hl hm] at hlo
  rw [three_path_scale n a₁ b₁ c₁ d₀ hn k l m hk hl hm] at hup
  exact ⟨hlo,hup⟩

end Oberwolfach
