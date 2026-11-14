module

public import Oberwolfach.MarkedWheels

@[expose] public section

/-! Counts at a fixed typed spoke. Canonical marked cycles have a fixed
marked position, so no choice of a cyclic starting point is counted twice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem one_position_indicator_total {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I]
    (i : I) (v : V) :
    (∑ C : I → V,if C i=v then (1:ℝ) else 0)=(Fintype.card V:ℝ)^(Fintype.card I-1) := by
  let S : Set (I → V) := {C | ∀ j∈({i}:Finset I),C j=v}
  have he := Finset.sum_congr_set S
    (fun C => if C i=v then (1:ℝ) else 0) (fun _ : S => (1:ℝ))
    (by intro C hC;exact if_pos (hC i (by simp)))
    (by intro C hC;apply if_neg;intro h;apply hC;intro j hj;simpa only [Finset.mem_singleton.mp hj] using h)
  rw [he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  change (Fintype.card {C : I → V // ∀ j∈({i}:Finset I),C j=(fun _ : I => v) j}:ℝ)=_
  rw [fixedCoordinates_card,Finset.card_singleton,Nat.cast_pow]

theorem marked_cycle_spoke_count {V E K : Type*} [Fintype V] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (j : Bool) (v : V) :
    (∑ C : MarkedCycleTuple tail head ktail khead m π b,markedSpokeIndicator C.val j v)≤
      (m+1)*(Fintype.card V:ℝ)^m := by
  apply (finite_subtype_sum_le (IsMarkedCycleTuple tail head ktail khead m π b)
    (fun C => markedSpokeIndicator C j v) (fun C => markedSpokeIndicator_nonneg C j v)).trans
  have hn : 0≤(Fintype.card V:ℝ)^m := by positivity
  cases j
  · simp only [markedSpokeIndicator,Bool.false_eq_true,ite_false]
    rw [Finset.sum_comm]
    have hh (i : Fin m) : (∑ C : Fin (m+1) → V,if C i.succ=v then (1:ℝ) else 0)=
        (Fintype.card V:ℝ)^m := by
      have he := one_position_indicator_total i.succ v
      simp only [Fintype.card_fin,Nat.add_sub_cancel] at he
      convert he using 1
      apply Finset.sum_congr rfl
      intro C _
      split_ifs <;> rfl
    simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    nlinarith
  · simp only [markedSpokeIndicator,ite_true]
    have hh := one_position_indicator_total (0:Fin (m+1)) v
    simp only [Fintype.card_fin,Nat.add_sub_cancel] at hh
    have he : (∑ C : Fin (m+1) → V,if C 0=v then (1:ℝ) else 0)=(Fintype.card V:ℝ)^m := by
      convert hh using 1
      apply Finset.sum_congr rfl
      intro C _
      split_ifs <;> rfl
    rw [he]
    nlinarith [show (0:ℝ)≤m by positivity]

theorem compatible_hub_single_count {V U : Type*} [Fintype U] [DecidableEq U] {m : ℕ}
    (H₀ Hₖ : V → U → Prop) (C : Fin (m+1) → V) (u : U) :
    (∑ h : {h // MarkedHubCompatible H₀ Hₖ C h},if h.val=u then (1:ℝ) else 0)≤1 := by
  have hh := finite_subtype_sum_le (MarkedHubCompatible H₀ Hₖ C)
    (fun h => if h=u then (1:ℝ) else 0) (fun h => by split_ifs <;> norm_num)
  simpa using hh

end Oberwolfach
