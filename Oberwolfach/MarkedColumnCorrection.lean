module

public import Oberwolfach.MarkedCommonTransferBounds
public import Oberwolfach.MarkedWheelCombinations
public import Oberwolfach.BalancedTransferAlgebra
public import Oberwolfach.PairTransferCoefficientBound

@[expose] public section

/-! The complete correction of marked and ordinary column sums, using
actual common-cycle transfers. Every coefficient and spoke bound includes
the cancellation of the hub-pair normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_column_correction {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (β M : ℝ) (hβ : 0<β) (hM : 0≤M) (hn : 0<Fintype.card V)
    (hcount : ∀ u u' : U,u≠u' → β*(Fintype.card V:ℝ)^(m+1)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'):ℝ))
    (B : U → ℝ) (hBsum : ∑ u,B u=0) (hB : ∀ u,|B u|≤M*Fintype.card V) :
    ∃ Ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad Ψ e=0) ∧
      (∀ j v,(∑ u,markedWheelSpokeLoad Ψ j v u)=0) ∧
      (∀ j u,(∑ v,markedWheelSpokeLoad Ψ j v u)=(if j then (1:ℝ) else m)*B u) ∧
      (∀ D,|Ψ D|≤4*M/(β*(Fintype.card V:ℝ)^m)) ∧
      (∀ j v u,|markedWheelSpokeLoad Ψ j v u|≤4*(m+1)*M/β) := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  let T (u u' : U) := markedCommonCycleTransfer (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
    (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) u u'
  have hquant (u u' : U) :
      (∀ D,|T u u' D|≤2/(β*(Fintype.card V:ℝ)^(m+1))) ∧
      (∀ j v h,|markedWheelSpokeLoad (T u u') j v h|≤2*(m+1)/(β*Fintype.card V)) := by
    by_cases he : u=u'
    · subst u'
      have ht : T u u=(fun _ => 0) := funext (markedCommonCycleTransfer_diagonal u)
      constructor
      · intro D;rw [ht,abs_zero];positivity
      · intro j v h
        rw [ht]
        simp only [markedWheelSpokeLoad,zero_mul,Finset.sum_const_zero,abs_zero]
        positivity
    · exact markedCommonCycleTransfer_quantitative u u' β hβ hn (hcount u u' he)
  have hcols (u u' : U) (j : Bool) (h : U) :
      (∑ v,markedWheelSpokeLoad (T u u') j v h)=
        (if j then (1:ℝ) else m)*((if h=u then 1 else 0)-(if h=u' then 1 else 0)) := by
    by_cases he : u=u'
    · subst u'
      have ht : T u u=(fun _ => 0) := funext (markedCommonCycleTransfer_diagonal u)
      rw [ht]
      simp only [markedWheelSpokeLoad,zero_mul,Finset.sum_const_zero,sub_self,mul_zero]
    · have hd : (0:ℝ)<β*(Fintype.card V:ℝ)^(m+1) := by positivity
      have hc : 0<Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u') := by
        exact_mod_cast hd.trans_le (hcount u u' he)
      exact markedCommonCycleTransfer_columns u u' hc j h
  let Ψ (D : MarkedWheel tail head ktail khead m π b H₀ Hₖ) : ℝ :=
    ∑ p : U×U,(B p.1/(Fintype.card U:ℝ))*T p.1 p.2 D
  refine ⟨Ψ,?_,?_,?_,?_,?_⟩
  · intro e
    unfold Ψ
    rw [markedWheelRimLoad_combination]
    simp only [T,markedCommonCycleTransfer_rim,mul_zero,Finset.sum_const_zero]
  · intro j v
    unfold Ψ
    rw [markedWheelSpokeLoad_row_combination]
    simp only [T,markedCommonCycleTransfer_zero_rows,mul_zero,Finset.sum_const_zero]
  · intro j h
    unfold Ψ
    rw [markedWheelSpokeLoad_column_combination]
    simp only [hcols,Fintype.sum_prod_type]
    have hh := balanced_pair_transfer_identity B hBsum h
    calc
      _ = (if j then (1:ℝ) else m)*
          ((∑ u,∑ u',(B u*((if h=u then (1:ℝ) else 0)-(if h=u' then 1 else 0))))/(Fintype.card U:ℝ)) := by
        simp only [Finset.sum_div,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro u' _
        ring
      _ = _ := by rw [hh]
  · intro D
    have hh := normalized_pair_transfer_bound (Function.Embedding.refl U) D.2.val B
      (fun u u' => T u u' D) (M*Fintype.card V) (2/(β*(Fintype.card V:ℝ)^(m+1)))
      (by positivity) (by positivity) hB (fun u u' => (hquant u u').1 D)
      (fun u u' hu hu' => markedCommonCycleTransfer_support u u' D hu hu')
    have he : Ψ D=(∑ p : U×U,B p.1*T p.1 p.2 D)/(Fintype.card U:ℝ) := by
      unfold Ψ
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [he]
    calc
      _ ≤ 2*(M*Fintype.card V)*(2/(β*(Fintype.card V:ℝ)^(m+1))) := hh
      _ = _ := by rw [pow_succ];field_simp <;> ring
  · intro j v h
    have hh := normalized_pair_transfer_bound (Function.Embedding.refl U) h B
      (fun u u' => markedWheelSpokeLoad (T u u') j v h) (M*Fintype.card V) (2*(m+1)/(β*Fintype.card V))
      (by positivity) (by positivity) hB (fun u u' => (hquant u u').2 j v h) (by
        intro u u' hu hu'
        change h≠u at hu
        change h≠u' at hu'
        rw [markedCommonCycleTransfer_spoke]
        simp only [hu,hu',ite_false,sub_self,zero_mul,zero_div])
    unfold Ψ
    rw [markedWheelSpokeLoad_combination]
    have he : (∑ p : U×U,(B p.1/(Fintype.card U:ℝ))*markedWheelSpokeLoad (T p.1 p.2) j v h)=
        (∑ p : U×U,B p.1*markedWheelSpokeLoad (T p.1 p.2) j v h)/(Fintype.card U:ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [he]
    calc
      _ ≤ 2*(M*Fintype.card V)*(2*(m+1)/(β*Fintype.card V)) := hh
      _ = _ := by field_simp <;> ring

end Oberwolfach
