module

public import Oberwolfach.OrdinaryWheelLoads

@[expose] public section

/-! Exact linearity of the two physical wheel-load maps under finite signed
linear combinations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weight_combination_test {I W : Type*} [Fintype I] [Fintype W]
    (a : I → ℝ) (T : I → W → ℝ) (t : W → ℝ) :
    (∑ w,(∑ i,a i*T i w)*t w)=∑ i,a i*(∑ w,T i w*t w) := by
  calc
    _ = ∑ w,∑ i,a i*(T i w*t w) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i,∑ w,a i*(T i w*t w) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

theorem ordinaryRimLoad_combination {V U I : Type*} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (a : I → ℝ) (T : I → OrdinaryWheel Q F H r → ℝ) (x y : V) :
    ordinaryRimLoad (fun W => ∑ i,a i*T i W) x y=∑ i,a i*ordinaryRimLoad (T i) x y := by
  let t (W : OrdinaryWheel Q F H r) : ℝ := if (ordinaryWheelRim W).Adj x y then 1 else 0
  have ht (w : OrdinaryWheel Q F H r → ℝ) :
      (∑ W,w W*t W)=ordinaryRimLoad w x y := by
    unfold ordinaryRimLoad
    apply Finset.sum_congr rfl
    intro W _
    dsimp only [t]
    split_ifs <;> simp
  rw [← ht,finite_weight_combination_test]
  simp only [ht]

theorem ordinarySpokeLoad_combination {V U I : Type*} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (a : I → ℝ) (T : I → OrdinaryWheel Q F H r → ℝ) (v : V) (u : U) :
    ordinarySpokeLoad (fun W => ∑ i,a i*T i W) v u=∑ i,a i*ordinarySpokeLoad (T i) v u := by
  let t (W : OrdinaryWheel Q F H r) : ℝ :=
    if ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support then 1 else 0
  have ht (w : OrdinaryWheel Q F H r → ℝ) :
      (∑ W,w W*t W)=ordinarySpokeLoad w v u := by
    unfold ordinarySpokeLoad
    apply Finset.sum_congr rfl
    intro W _
    dsimp only [t]
    split_ifs <;> simp
  rw [← ht,finite_weight_combination_test]
  simp only [ht]

end Oberwolfach
