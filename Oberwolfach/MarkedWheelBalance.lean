module

public import Oberwolfach.MarkedCycleRowIdentities

@[expose] public section

/-! Balance identities for arbitrary signed marked-wheel weights. The rim
and spoke sums retain their types and actual hubs throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedWheelRimLoad_vector {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) :
    markedWheelRimLoad ψ=∑ W,ψ W • markedCycleIncidence tail head ktail khead m W.1.val := by
  funext e
  simp only [markedWheelRimLoad,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem markedWheelRimLoad_balanced {V U E K : Type*} [Fintype V] [Fintype U]
    [Fintype E] [Fintype K] [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) :
    markedWheelRimLoad ψ∈markedBalanceSubspace tail head ktail khead m := by
  rw [markedWheelRimLoad_vector]
  apply Submodule.sum_mem
  intro W _
  apply Submodule.smul_mem
  exact markedCycleIncidence_balanced tail head ktail khead hinj hkinj m W.1.val W.1.property.2.1 W.1.property.2.2

theorem markedWheelSpokeLoad_row {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (j : Bool) (v : V) :
    (∑ u,markedWheelSpokeLoad ψ j v u)=∑ W,ψ W*markedSpokeIndicator W.1.val j v := by
  unfold markedWheelSpokeLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W _
  simp

theorem markedWheelSpokeLoad_column {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (j : Bool) (u : U) :
    (∑ v,markedWheelSpokeLoad ψ j v u)=
      (if j then (1:ℝ) else m)*(∑ W,if W.2.val=u then ψ W else 0) := by
  unfold markedWheelSpokeLoad
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W _
  by_cases hu : W.2.val=u
  · simp only [if_pos hu]
    rw [← Finset.mul_sum,markedSpokeIndicator_total]
    ring
  · simp only [if_neg hu,mul_zero,Finset.sum_const_zero]

theorem markedWheelSpokeLoad_column_ratio {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (u : U) :
    (∑ v,markedWheelSpokeLoad ψ false v u)=(m:ℝ)*(∑ v,markedWheelSpokeLoad ψ true v u) := by
  rw [markedWheelSpokeLoad_column ψ false u,markedWheelSpokeLoad_column ψ true u]
  simp

theorem markedWheelRimLoad_outgoing {V U E K : Type*} [Fintype V] [Fintype U]
    [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (v : V) :
    occurrenceSumLinear (Sum.elim tail ktail) (markedWheelRimLoad ψ) v=
      (∑ u,markedWheelSpokeLoad ψ false v u)+(∑ u,markedWheelSpokeLoad ψ true v u) := by
  rw [markedWheelRimLoad_vector,map_sum]
  simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    markedCycleIncidence_outgoing tail head ktail khead hinj hkinj m π b]
  rw [markedWheelSpokeLoad_row,markedWheelSpokeLoad_row]
  simp only [mul_add,Finset.sum_add_distrib]

theorem markedWheelRimLoad_marked_head {V U E K : Type*} [Fintype V] [Fintype U]
    [Fintype K] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (v : V) :
    occurrenceSumLinear khead (fun e => markedWheelRimLoad ψ (Sum.inr e)) v=
      ∑ u,markedWheelSpokeLoad ψ true v u := by
  have he : (fun e => markedWheelRimLoad ψ (Sum.inr e))=
      ∑ W,ψ W • (fun e => markedCycleIncidence tail head ktail khead m W.1.val (Sum.inr e)) := by
    funext e
    simp only [markedWheelRimLoad,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he,map_sum]
  simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    markedCycleIncidence_marked_head tail head ktail khead hkinj m π b]
  exact (markedWheelSpokeLoad_row ψ true v).symm

theorem markedWheelRimLoad_nonzero_separated {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} (hm : 1≤m) {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e : E⊕K)
    (he : markedWheelRimLoad ψ e≠0) :
    ¬PermutationClose π b (Sum.elim tail ktail e) (Sum.elim head khead e) := by
  intro hc
  apply he
  unfold markedWheelRimLoad
  apply Finset.sum_eq_zero
  intro W _
  rw [marked_cycle_zero_on_close_arc tail head ktail khead m hm π b W.1 e hc,mul_zero]

end Oberwolfach
