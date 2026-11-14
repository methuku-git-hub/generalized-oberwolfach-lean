module

public import Oberwolfach.MarkedCycleCountBounds
public import Oberwolfach.PositiveBoundedCoefficients

@[expose] public section

/-! Exact positive coefficients on the fixed family of marked cycles. The
preliminary positive load is bounded by counting cycles through each typed edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_cycle_positive_baseline {V E K : Type*}
    [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (hm : 1≤m)
    (π : Equiv.Perm V) (b : ℕ) (κ : ℝ) (hκ : 0<κ) (hn : 0<Fintype.card V) :
    ‖∑ C : MarkedCycleTuple tail head ktail khead m π b,
      ((κ/(4*(m:ℝ)))/(Fintype.card V:ℝ)^(m-1)) •
        markedCycleIncidence tail head ktail khead m C.val‖≤κ/4 := by
  have hmr : (0:ℝ)<m := Nat.cast_pos.mpr (by omega)
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hnPow : 0<(Fintype.card V:ℝ)^(m-1) := pow_pos hnr _
  have hc : 0≤(κ/(4*(m:ℝ)))/(Fintype.card V:ℝ)^(m-1) := by positivity
  apply (pi_norm_le_iff_of_nonneg (show 0≤κ/4 by positivity)).mpr
  intro e
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,Real.norm_eq_abs]
  have hnSum : 0≤∑ C : MarkedCycleTuple tail head ktail khead m π b,
      markedCycleIncidence tail head ktail khead m C.val e :=
    Finset.sum_nonneg (fun C _ => markedCycleIncidence_nonneg tail head ktail khead m C.val e)
  rw [abs_of_nonneg (mul_nonneg hc hnSum)]
  have hh := mul_le_mul_of_nonneg_left (marked_cycle_incidence_count tail head ktail khead m hm π b e) hc
  have he : ((κ/(4*(m:ℝ)))/(Fintype.card V:ℝ)^(m-1))*
      ((m:ℝ)*(Fintype.card V:ℝ)^(m-1))=κ/4 := by field_simp
  exact he ▸ hh

set_option maxHeartbeats 1000000 in
theorem exact_positive_marked_cycle_weights {V E K : Type*}
    [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V)
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (m : ℕ) (hm : 1≤m) (π : Equiv.Perm V) (b : ℕ) (hn : 0<Fintype.card V)
    (w : E⊕K → ℝ) (κ η B : ℝ) (hκ : 0<κ) (hη : η<κ/4)
    (hw : w∈markedBalanceSubspace tail head ktail khead m)
    (hwclose : ‖w-(fun _ => (1:ℝ))‖≤κ/4)
    (happrox : ∀ w'∈markedBalanceSubspace tail head ktail khead m,
      ‖w'-(fun _ => (1:ℝ))‖≤κ →
      ∃ a : MarkedCycleTuple tail head ktail khead m π b → ℝ,
        (∀ C,0≤a C ∧ a C≤B/(Fintype.card V:ℝ)^(m-1)) ∧
        ‖(∑ C,a C • markedCycleIncidence tail head ktail khead m C.val)-w'‖≤η) :
    ∃ a : MarkedCycleTuple tail head ktail khead m π b → ℝ,
      (∀ C,0<a C ∧ (κ/(4*(m:ℝ)))/(Fintype.card V:ℝ)^(m-1)≤a C ∧
        a C≤(κ/(4*(m:ℝ))+B)/(Fintype.card V:ℝ)^(m-1)) ∧
      (∑ C,a C • markedCycleIncidence tail head ktail khead m C.val)=w := by
  let S := markedBalanceSubspace tail head ktail khead m
  let P (C : MarkedCycleTuple tail head ktail khead m π b) :=
    markedCycleIncidence tail head ktail khead m C.val
  have hP (C : MarkedCycleTuple tail head ktail khead m π b) : P C∈S :=
    markedCycleIncidence_balanced tail head ktail khead hinj hkinj m C.val C.property.2.1 C.property.2.2
  have hmr : (0:ℝ)<m := Nat.cast_pos.mpr (by omega)
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  obtain ⟨a,ha,he⟩ := subspace_positive_bounded_coefficients S P hP (fun _ => 1) w hw
    κ η (B/(Fintype.card V:ℝ)^(m-1)) ((κ/(4*(m:ℝ)))/(Fintype.card V:ℝ)^(m-1))
    hκ (by positivity) hη hwclose
    (marked_cycle_positive_baseline tail head ktail khead m hm π b κ hκ hn) happrox
  refine ⟨a,?_,he⟩
  intro C
  obtain ⟨hp,hl,hu⟩ := ha C
  exact ⟨hp,hl,by simpa only [add_div] using hu⟩

end Oberwolfach
