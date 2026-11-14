module

public import Oberwolfach.TransferConfigurationCounts
public import Oberwolfach.FiniteSignedAverages

@[expose] public section

/-! Averaging all labelled configurations preserves the exact transfer and
bounds each physical wheel coefficient by its number of fixed free labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryAverageTransfer {V U : Type*} [Fintype V] {r : ℕ} (hr : 3≤r)
    (Q F : SimpleGraph V) (H : V → U → Prop) (v : V) (u u' : U) : OrdinaryWheel Q F H r → ℝ :=
  finiteSignedAverage (fun T : OrdinaryTransferConfiguration hr Q F H v u u' => T.weight)

theorem ordinaryAverageTransfer_loads {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] {r : ℕ} (hr : 3≤r)
    (Q F : SimpleGraph V) (H : V → U → Prop) (v : V) (u u' : U)
    (hT : 0<Fintype.card (OrdinaryTransferConfiguration hr Q F H v u u')) :
    (∀ x y,ordinaryRimLoad (ordinaryAverageTransfer hr Q F H v u u') x y=0) ∧
    (∀ z h,ordinarySpokeLoad (ordinaryAverageTransfer hr Q F H v u u') z h=
      (if z=v then (1:ℝ) else 0)*((if h=u then 1 else 0)-(if h=u' then 1 else 0))) := by
  constructor
  · intro x y
    exact finiteSignedAverage_indicator_constant hT
      (fun T : OrdinaryTransferConfiguration hr Q F H v u u' => T.weight)
      (fun W => (ordinaryWheelRim W).Adj x y) 0 (fun T => T.loads.1 x y)
  · intro z h
    let t (W : OrdinaryWheel Q F H r) : ℝ :=
      if ordinaryWheelHub W=h ∧ z∈(ordinaryWheelRim W).support then 1 else 0
    let K : ℝ := (if z=v then (1:ℝ) else 0)*((if h=u then 1 else 0)-(if h=u' then 1 else 0))
    have htest (T : OrdinaryTransferConfiguration hr Q F H v u u') :
        (∑ W : OrdinaryWheel Q F H r,T.weight W*t W)=K := by
      calc
        _ = ordinarySpokeLoad T.weight z h := by
          unfold ordinarySpokeLoad
          apply Finset.sum_congr rfl
          intro W _
          dsimp only [t]
          split_ifs <;> simp
        _ = _ := T.loads.2 z h
    have hh := finiteSignedAverage_constant_test hT
      (fun T : OrdinaryTransferConfiguration hr Q F H v u u' => T.weight) t K htest
    calc
      _ = ∑ W : OrdinaryWheel Q F H r,
          finiteSignedAverage (fun T : OrdinaryTransferConfiguration hr Q F H v u u' => T.weight) W*t W := by
        unfold ordinarySpokeLoad ordinaryAverageTransfer
        apply Finset.sum_congr rfl
        intro W _
        dsimp only [t]
        split_ifs <;> simp
      _ = K := hh

theorem ordinaryAverageTransfer_zero_other_hubs {V U : Type*} [Fintype V]
    {r : ℕ} (hr : 3≤r) (Q F : SimpleGraph V) (H : V → U → Prop)
    (v : V) (u u' : U) (D : OrdinaryWheel Q F H r)
    (hu : ordinaryWheelHub D≠u) (hu' : ordinaryWheelHub D≠u') :
    ordinaryAverageTransfer hr Q F H v u u' D=0 := by
  apply finiteSignedAverage_eq_zero
  intro T
  by_contra hn
  exact ((T.weight_support D hn).1).elim hu hu'

theorem ordinaryAverageTransfer_erased_bound {V U : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 3≤r) (Q F : SimpleGraph V) (H : V → U → Prop)
    (v : V) (u u' : U) (γ : ℝ) (hγ : 0<γ) (hn : 0<Fintype.card V)
    (hT : γ*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr Q F H v u u'):ℝ))
    (D : OrdinaryWheel Q F H r) :
    |ordinaryAverageTransfer hr Q F H v u u' D|≤
      (6*((r:ℝ)^2)^((ordinaryWheelRim D).support.toFinset.erase v).card/γ)/
        (Fintype.card V:ℝ)^((ordinaryWheelRim D).support.toFinset.erase v).card := by
  let s := ((ordinaryWheelRim D).support.toFinset.erase v).card
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hden : 0<γ*(Fintype.card V:ℝ)^(r^2) := by positivity
  have hs : s≤r^2 := by
    have hh := Finset.card_erase_le (s:=(ordinaryWheelRim D).support.toFinset) (a:=v)
    have hc := D.val.1.val.property.support_card
    change (ordinaryWheelRim D).support.toFinset.card=r at hc
    dsimp [s]
    rw [hc] at hh
    nlinarith
  calc
    _ ≤ (∑ T : OrdinaryTransferConfiguration hr Q F H v u u',|T.weight D|)/
        (Fintype.card (OrdinaryTransferConfiguration hr Q F H v u u'):ℝ) := finiteSignedAverage_abs_le _ _
    _ ≤ (∑ T : OrdinaryTransferConfiguration hr Q F H v u u',|T.weight D|)/
        (γ*(Fintype.card V:ℝ)^(r^2)) :=
      div_le_div_of_nonneg_left (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hden hT
    _ ≤ (6*((r:ℝ)^2)^s*(Fintype.card V:ℝ)^(r^2-s))/
        (γ*(Fintype.card V:ℝ)^(r^2)) :=
      div_le_div_of_nonneg_right (ordinary_transfer_coefficient_sum_bound (hr:=hr) (v:=v) (u:=u) (u':=u') D) hden.le
    _ = _ := by
      change (6*((r:ℝ)^2)^s*(Fintype.card V:ℝ)^(r^2-s))/
        (γ*(Fintype.card V:ℝ)^(r^2))=(6*((r:ℝ)^2)^s/γ)/(Fintype.card V:ℝ)^s
      have hp : (Fintype.card V:ℝ)^(r^2)=
          (Fintype.card V:ℝ)^(r^2-s)*(Fintype.card V:ℝ)^s := by
        rw [← pow_add,Nat.sub_add_cancel hs]
      rw [hp]
      field_simp

theorem ordinaryAverageTransfer_coefficient_bound {V U : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 3≤r) (Q F : SimpleGraph V) (H : V → U → Prop)
    (v : V) (u u' : U) (γ : ℝ) (hγ : 0<γ) (hn : 0<Fintype.card V)
    (hT : γ*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr Q F H v u u'):ℝ))
    (D : OrdinaryWheel Q F H r) :
    |ordinaryAverageTransfer hr Q F H v u u' D|≤
      if v∈(ordinaryWheelRim D).support then
        (6*((r:ℝ)^2)^r/γ)/(Fintype.card V:ℝ)^(r-1)
      else (6*((r:ℝ)^2)^r/γ)/(Fintype.card V:ℝ)^r := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hr' : (3:ℝ)≤r := by exact_mod_cast hr
  have hc : (ordinaryWheelRim D).support.toFinset.card=r := D.val.1.val.property.support_card
  have hs : ((ordinaryWheelRim D).support.toFinset.erase v).card≤r := by
    have hh := Finset.card_erase_le (s:=(ordinaryWheelRim D).support.toFinset) (a:=v)
    simpa only [hc] using hh
  have hp := pow_le_pow_right₀ (show (1:ℝ)≤(r:ℝ)^2 by nlinarith) hs
  have hh := (ordinaryAverageTransfer_erased_bound hr Q F H v u u' γ hγ hn hT D).trans
    (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤6)) hγ.le)
      (by positivity))
  by_cases hv : v∈(ordinaryWheelRim D).support
  · have hve : v∈(ordinaryWheelRim D).support.toFinset := Set.mem_toFinset.mpr hv
    rw [if_pos hv]
    simpa only [Finset.card_erase_of_mem hve,hc] using hh
  · have hve : v∉(ordinaryWheelRim D).support.toFinset := by simpa only [Set.mem_toFinset] using hv
    rw [if_neg hv]
    simpa only [Finset.erase_eq_of_notMem hve,hc] using hh

end Oberwolfach
