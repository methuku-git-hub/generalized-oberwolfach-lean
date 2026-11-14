module

public import Oberwolfach.MarkedSpokeCounts

@[expose] public section

/-! Splitting a signed cycle coefficient equally among its actual compatible
hubs preserves the rim vector. The coefficient and spoke bounds use these
same, fixed hub sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedWheelLift {V U E K : Type*} [Fintype U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    (H₀ Hₖ : V → U → Prop) (q : MarkedCycleTuple tail head ktail khead m π b → ℝ)
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) : ℝ :=
  q W.1/(Fintype.card {u // MarkedHubCompatible H₀ Hₖ W.1.val u}:ℝ)

theorem markedWheelLift_test {V U E K : Type*} [Fintype V] [Fintype U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    (H₀ Hₖ : V → U → Prop) (q t : MarkedCycleTuple tail head ktail khead m π b → ℝ)
    (hhub : ∀ C : MarkedCycleTuple tail head ktail khead m π b,
      0<Fintype.card {u // MarkedHubCompatible H₀ Hₖ C.val u}) :
    (∑ W : MarkedWheel tail head ktail khead m π b H₀ Hₖ,
      markedWheelLift H₀ Hₖ q W*t W.1)=∑ C,q C*t C := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro C _
  change (∑ _h : {u // MarkedHubCompatible H₀ Hₖ C.val u},
    q C/(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C.val u}:ℝ)*t C)=q C*t C
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : (Fintype.card {u // MarkedHubCompatible H₀ Hₖ C.val u}:ℝ)≠0 :=
    (Nat.cast_pos.mpr (hhub C)).ne'
  field_simp

theorem markedWheelLift_rim {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    (H₀ Hₖ : V → U → Prop) (q : MarkedCycleTuple tail head ktail khead m π b → ℝ)
    (hhub : ∀ C : MarkedCycleTuple tail head ktail khead m π b,
      0<Fintype.card {u // MarkedHubCompatible H₀ Hₖ C.val u}) (e : E⊕K) :
    markedWheelRimLoad (markedWheelLift H₀ Hₖ q) e=
      ∑ C,q C*markedCycleIncidence tail head ktail khead m C.val e :=
  markedWheelLift_test H₀ Hₖ q (fun C => markedCycleIncidence tail head ktail khead m C.val e) hhub

theorem markedWheelLift_bound {V U E K : Type*} [Fintype V] [Fintype U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} (hm : 1≤m) {π : Equiv.Perm V} {b : ℕ}
    (H₀ Hₖ : V → U → Prop) (q : MarkedCycleTuple tail head ktail khead m π b → ℝ)
    (β B : ℝ) (hβ : 0<β) (hB : 0≤B) (hn : 0<Fintype.card V)
    (hhub : ∀ C : MarkedCycleTuple tail head ktail khead m π b,
      β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C.val u}:ℝ))
    (hq : ∀ C,|q C|≤B/(Fintype.card V:ℝ)^(m-1))
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    |markedWheelLift H₀ Hₖ q W|≤(B/β)/(Fintype.card V:ℝ)^m := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hd : 0<β*Fintype.card V := by positivity
  have hc := hd.trans_le (hhub W.1)
  unfold markedWheelLift
  rw [abs_div,abs_of_nonneg hc.le]
  calc
    _ ≤ |q W.1|/(β*Fintype.card V) := div_le_div_of_nonneg_left (abs_nonneg _) hd (hhub W.1)
    _ ≤ (B/(Fintype.card V:ℝ)^(m-1))/(β*Fintype.card V) :=
      div_le_div_of_nonneg_right (hq W.1) hd.le
    _ = _ := by
      have hp : (Fintype.card V:ℝ)^m=(Fintype.card V:ℝ)^(m-1)*(Fintype.card V:ℝ) := by
        rw [← pow_succ,show m-1+1=m by omega]
      rw [hp];field_simp

theorem markedWheelSpokeLoad_coefficient_bound {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (M : ℝ) (hM : 0≤M) (hψ : ∀ W,|ψ W|≤M) (j : Bool) (v : V) (u : U) :
    |markedWheelSpokeLoad ψ j v u|≤M*((m+1)*(Fintype.card V:ℝ)^m) := by
  have hterm (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
      |ψ W*(if W.2.val=u then markedSpokeIndicator W.1.val j v else 0)|≤
      M*(if W.2.val=u then markedSpokeIndicator W.1.val j v else 0) := by
    have hn : 0≤(if W.2.val=u then markedSpokeIndicator W.1.val j v else 0) := by
      split_ifs
      · exact markedSpokeIndicator_nonneg _ _ _
      · norm_num
    rw [abs_mul,abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_right (hψ W) hn
  have hsingle (C : MarkedCycleTuple tail head ktail khead m π b) :
      (∑ h : {h // MarkedHubCompatible H₀ Hₖ C.val h},
        if h.val=u then markedSpokeIndicator C.val j v else 0)≤markedSpokeIndicator C.val j v := by
    have hh := compatible_hub_single_count H₀ Hₖ C.val u
    calc
      _ = (∑ h : {h // MarkedHubCompatible H₀ Hₖ C.val h},if h.val=u then (1:ℝ) else 0)*
          markedSpokeIndicator C.val j v := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro h _
        split_ifs <;> simp
      _ ≤ 1*markedSpokeIndicator C.val j v :=
        mul_le_mul_of_nonneg_right hh (markedSpokeIndicator_nonneg _ _ _)
      _ = _ := one_mul _
  unfold markedWheelSpokeLoad
  calc
    _ ≤ ∑ W,|ψ W*(if W.2.val=u then markedSpokeIndicator W.1.val j v else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ W,M*(if W.2.val=u then markedSpokeIndicator W.1.val j v else 0) := Finset.sum_le_sum (fun W _ => hterm W)
    _ = M*(∑ C,∑ h : {h // MarkedHubCompatible H₀ Hₖ C.val h},
        if h.val=u then markedSpokeIndicator C.val j v else 0) := by rw [← Finset.mul_sum,Fintype.sum_sigma]
    _ ≤ M*(∑ C : MarkedCycleTuple tail head ktail khead m π b,markedSpokeIndicator C.val j v) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun C _ => hsingle C)) hM
    _ ≤ _ := mul_le_mul_of_nonneg_left (marked_cycle_spoke_count tail head ktail khead m π b j v) hM

end Oberwolfach
