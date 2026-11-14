module

public import Oberwolfach.MarkedCommonCycleTransfers

@[expose] public section

/-! Actual column masses, zero row sums, and quantitative bounds for the
common-cycle transfer. These use the same common-cycle denominator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

section
variable {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
variable {H₀ Hₖ : V → U → Prop}

 theorem markedCommonCycleTransfer_zero_rows (u u' : U) (j : Bool) (v : V) :
    (∑ h,markedWheelSpokeLoad (markedCommonCycleTransfer (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) u u') j v h)=0 := by
  simp_rw [markedCommonCycleTransfer_spoke]
  rw [← Finset.sum_div,← Finset.sum_mul]
  simp

 theorem markedCommonCycleTransfer_columns (u u' : U)
    (hcount : 0<Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'))
    (j : Bool) (h : U) :
    (∑ v,markedWheelSpokeLoad (markedCommonCycleTransfer (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) u u') j v h)=
      (if j then (1:ℝ) else m)*((if h=u then 1 else 0)-(if h=u' then 1 else 0)) := by
  have hc : (Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'):ℝ)≠0 :=
    (Nat.cast_pos.mpr hcount).ne'
  simp_rw [markedCommonCycleTransfer_spoke]
  rw [← Finset.sum_div,← Finset.mul_sum,Finset.sum_comm]
  simp only [markedSpokeIndicator_total,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

 theorem markedCommonCycleTransfer_quantitative (u u' : U) (β : ℝ) (hβ : 0<β) (hn : 0<Fintype.card V)
    (hcount : β*(Fintype.card V:ℝ)^(m+1)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'):ℝ)) :
    (∀ D : MarkedWheel tail head ktail khead m π b H₀ Hₖ,
      |markedCommonCycleTransfer u u' D|≤2/(β*(Fintype.card V:ℝ)^(m+1))) ∧
    (∀ j v h,|markedWheelSpokeLoad (markedCommonCycleTransfer (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) u u') j v h|≤2*(m+1)/(β*Fintype.card V)) := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hd : (0:ℝ)<β*(Fintype.card V:ℝ)^(m+1) := by positivity
  have hc := hd.trans_le hcount
  constructor
  · intro D
    exact (markedCommonCycleTransfer_bound u u' D).trans
      (div_le_div_of_nonneg_left (by norm_num) hd hcount)
  · intro j v h
    have hδ : |(if h=u then (1:ℝ) else 0)-(if h=u' then 1 else 0)|≤2 := by
      split_ifs <;> norm_num
    have hsum : (∑ C : CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u',
        markedSpokeIndicator C.val.val j v)≤(m+1)*(Fintype.card V:ℝ)^m := by
      have hh := (finite_subtype_sum_le (fun C : MarkedCycleTuple tail head ktail khead m π b =>
        MarkedHubCompatible H₀ Hₖ C.val u ∧ MarkedHubCompatible H₀ Hₖ C.val u')
        (fun C => markedSpokeIndicator C.val j v) (fun C => markedSpokeIndicator_nonneg _ _ _)).trans
        (marked_cycle_spoke_count tail head ktail khead m π b j v)
      convert hh using 1
      apply Finset.sum_congr
      · ext C
        simp
      · intro C _
        rfl
    have hnonneg : 0≤∑ C : CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u',
        markedSpokeIndicator C.val.val j v := Finset.sum_nonneg (fun C _ => markedSpokeIndicator_nonneg _ _ _)
    rw [markedCommonCycleTransfer_spoke,abs_div,abs_mul,abs_of_nonneg hnonneg,abs_of_pos hc]
    calc
      _ ≤ (2*((m+1)*(Fintype.card V:ℝ)^m))/
          (Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'):ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul hδ hsum hnonneg (by norm_num)) hc.le
      _ ≤ (2*((m+1)*(Fintype.card V:ℝ)^m))/(β*(Fintype.card V:ℝ)^(m+1)) :=
        div_le_div_of_nonneg_left (by positivity) hd hcount
      _ = _ := by rw [pow_succ];field_simp

 theorem markedCommonCycleTransfer_diagonal (u : U) (D : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    markedCommonCycleTransfer u u D=0 := by
  unfold markedCommonCycleTransfer averagedBasisDifference
  apply finiteSignedAverage_eq_zero
  intro C
  simp only [commonMarkedWheelLeft,commonMarkedWheelRight,Function.Embedding.coeFn_mk,sub_self]

end
end Oberwolfach
