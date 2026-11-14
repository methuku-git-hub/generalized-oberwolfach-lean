module

public import Oberwolfach.FractionalDegrees

@[expose] public section

/-! Normalisation of signed degree corrections retains the original degree
scale and the zero total of each correction function. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def occurrenceDegree {V E : Type*} [Fintype E] (f : E → V) (v : V) : ℝ :=
  ∑ e,if f e=v then 1 else 0

theorem occurrenceDegree_nonneg {V E : Type*} [Fintype E] (f : E → V) (v : V) :
    0≤occurrenceDegree f v := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> norm_num

theorem occurrenceDegree_total {V E : Type*} [Fintype V] [Fintype E] (f : E → V) :
    (∑ v,occurrenceDegree f v)=(Fintype.card E : ℝ) := by
  simp only [occurrenceDegree]
  rw [Finset.sum_comm]
  simp

theorem normalized_signed_demand_total {V E : Type*} [Fintype V] [Fintype E]
    (f : E → V) (Δ : V → ℝ) (hΔ : ∑ v,Δ v=0) (s B : ℝ) (hs : 0<s) :
    (∑ v,(s*occurrenceDegree f v+Δ v)/(B*s))=(Fintype.card E : ℝ)/B := by
  rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum,occurrenceDegree_total,hΔ]
  field_simp [hs.ne']
  <;> ring

theorem normalized_signed_demand_bounds
    (degree Δ E n s B δ ε r : ℝ) (hE : 0≤E) (hn : 0<n) (hs : 0<s) (hB : 1≤B)
    (hδ : 0≤δ) (hδsmall : δ<1/4)
    (hdeg : |degree-E/n|≤ε) (hΔ : |Δ|≤r)
    (hsmall : s*ε+r ≤ δ*s*(E/n)) :
    0≤(s*degree+Δ)/(B*s) ∧
      (s*degree+Δ)/(B*s) ≤ (1+δ)*(E/B)/n := by
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hcenter : 0≤s*(E/n) := mul_nonneg hs.le (div_nonneg hE hn.le)
  have herror : |s*degree+Δ-s*(E/n)| ≤ δ*s*(E/n) := by
    rw [show s*degree+Δ-s*(E/n)=s*(degree-E/n)+Δ by ring]
    calc
      _ ≤ |s*(degree-E/n)|+|Δ| := abs_add_le _ _
      _ = s*|degree-E/n|+|Δ| := by rw [abs_mul,abs_of_pos hs]
      _ ≤ s*ε+r := add_le_add (mul_le_mul_of_nonneg_left hdeg hs.le) hΔ
      _ ≤ _ := hsmall
  obtain ⟨hlo,hup⟩ := abs_le.mp herror
  have hmul : δ*(s*(E/n)) ≤ s*(E/n) := mul_le_of_le_one_left hcenter (by linarith)
  have hg : 0≤s*degree+Δ := by nlinarith
  refine ⟨div_nonneg hg (mul_pos hBp hs).le,?_⟩
  have hgu : s*degree+Δ ≤ (1+δ)*s*(E/n) := by nlinarith
  have hh := div_le_div_of_nonneg_right hgu (mul_pos hBp hs).le
  convert hh using 1 <;> field_simp [hs.ne',hBp.ne',hn.ne']

end Oberwolfach
