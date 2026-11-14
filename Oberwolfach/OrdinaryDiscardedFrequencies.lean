module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Discarding every short length below its fixed frequency cutoff loses
at most the number of possible lengths times that cutoff. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
open scoped BigOperators

theorem ordinary_discarded_short_frequency (K:ℕ) (hK:0<K) (θ:ℝ) (hθ:0≤θ)
    (f:Fin K→ℝ) (hf:∀ i,0≤f i):
    0≤∑ i:Fin K,(if f i<θ/(100*(K:ℝ)) then f i else 0) ∧
    (∑ i:Fin K,(if f i<θ/(100*(K:ℝ)) then f i else 0))≤θ/100 := by
  have hK0:(0:ℝ)<K:=by exact_mod_cast hK
  have hcut:0≤θ/(100*(K:ℝ)):=by positivity
  have hpoint:∀ i:Fin K,(if f i<θ/(100*(K:ℝ)) then f i else 0)≤θ/(100*(K:ℝ)):=by
    intro i
    split_ifs with h
    · exact h.le
    · exact hcut
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hpoint i)
  have heq:(∑ _i:Fin K,θ/(100*(K:ℝ)))=θ/100:=by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  refine ⟨?_,?_⟩
  · apply Finset.sum_nonneg
    intro i _
    split_ifs <;> simp [hf]
  · exact hsum.trans_eq heq
end Oberwolfach
