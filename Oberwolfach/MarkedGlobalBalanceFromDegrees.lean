module

public import Oberwolfach.SparseTypedHostCorrection

@[expose] public section
/-! Degree and spoke concentration with matching targets imply the four
near-balance estimates needed by sparse marked correction. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_global_balance_from_degree_approximations
    {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (m:ℕ)
    (pD kD sCol tCol errR errS errC:ℝ)
    (hcolTarget:sCol=(m:ℝ)*tCol)
    (htail:∀v,|occurrenceDegree tail v-pD|≤errR)
    (hhead:∀v,|occurrenceDegree head v-pD|≤errR)
    (hktail:∀v,|occurrenceDegree ktail v-kD|≤errR)
    (hkhead:∀v,|occurrenceDegree khead v-kD|≤errR)
    (hrow0:∀v,|(∑u,if H₀ v u then (1:ℝ) else 0)-pD|≤errS)
    (hrowK:∀v,|(∑u,if HK v u then (1:ℝ) else 0)-kD|≤errS)
    (hcol0:∀u,|(∑v,if H₀ v u then (1:ℝ) else 0)-sCol|≤errC)
    (hcolK:∀u,|(∑v,if HK v u then (1:ℝ) else 0)-tCol|≤errC):
    (∀v,|occurrenceDegree (Sum.elim tail ktail) v-
      (∑u,if H₀ v u then (1:ℝ) else 0)-(∑u,if HK v u then (1:ℝ) else 0)|≤2*errR+2*errS) ∧
    (∀v,|occurrenceDegree (Sum.elim head khead) v-
      (∑u,if H₀ v u then (1:ℝ) else 0)-(∑u,if HK v u then (1:ℝ) else 0)|≤2*errR+2*errS) ∧
    (∀v,|occurrenceDegree khead v-(∑u,if HK v u then (1:ℝ) else 0)|≤errR+errS) ∧
    (∀u,|(∑v,if H₀ v u then (1:ℝ) else 0)-(m:ℝ)*(∑v,if HK v u then (1:ℝ) else 0)|≤((m:ℝ)+1)*errC):=by
  have hsum (f:E→V) (g:K→V) (v:V):
      occurrenceDegree (Sum.elim f g) v=occurrenceDegree f v+occurrenceDegree g v:=by
    simp only [occurrenceDegree,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> split_ifs <;> rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    rw [hsum]
    have ha:=abs_le.mp (htail v);have hb:=abs_le.mp (hktail v)
    have hc:=abs_le.mp (hrow0 v);have hd:=abs_le.mp (hrowK v)
    apply abs_le.mpr;constructor <;> linarith
  · intro v
    rw [hsum]
    have ha:=abs_le.mp (hhead v);have hb:=abs_le.mp (hkhead v)
    have hc:=abs_le.mp (hrow0 v);have hd:=abs_le.mp (hrowK v)
    apply abs_le.mpr;constructor <;> linarith
  · intro v
    have ha:=abs_le.mp (hkhead v);have hb:=abs_le.mp (hrowK v)
    apply abs_le.mpr;constructor <;> linarith
  · intro u
    have ha:=abs_le.mp (hcol0 u);have hb:=abs_le.mp (hcolK u)
    have hm:0≤(m:ℝ):=Nat.cast_nonneg _
    have hc:=mul_le_mul_of_nonneg_left hb.1 hm
    have hd:=mul_le_mul_of_nonneg_left hb.2 hm
    apply abs_le.mpr;constructor <;> nlinarith [hcolTarget]
end Oberwolfach
