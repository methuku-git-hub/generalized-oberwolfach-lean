module

public import Oberwolfach.MarkedWheels

@[expose] public section

/-! Linearity of typed wheel loads for the actual finite wheel family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

section
variable {V U E K I : Type*} [Fintype V] [Fintype U] [Fintype I]
variable [DecidableEq V] [DecidableEq U]
variable {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
variable {H₀ Hₖ : V → U → Prop}
variable (a : I → ℝ) (T : I → MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)

 theorem markedWheelRimLoad_combination (e : E⊕K) :
    markedWheelRimLoad (fun D => ∑ i,a i*T i D) e=∑ i,a i*markedWheelRimLoad (T i) e :=
  finite_weight_combination_test a T (fun D => markedCycleIncidence tail head ktail khead m D.1.val e)

 theorem markedWheelSpokeLoad_combination (j : Bool) (v : V) (u : U) :
    markedWheelSpokeLoad (fun D => ∑ i,a i*T i D) j v u=∑ i,a i*markedWheelSpokeLoad (T i) j v u :=
  finite_weight_combination_test a T (fun D => if D.2.val=u then markedSpokeIndicator D.1.val j v else 0)

 theorem markedWheelSpokeLoad_row_combination (j : Bool) (v : V) :
    (∑ u,markedWheelSpokeLoad (fun D => ∑ i,a i*T i D) j v u)=
      ∑ i,a i*(∑ u,markedWheelSpokeLoad (T i) j v u) := by
  simp_rw [markedWheelSpokeLoad_combination]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

 theorem markedWheelSpokeLoad_column_combination (j : Bool) (u : U) :
    (∑ v,markedWheelSpokeLoad (fun D => ∑ i,a i*T i D) j v u)=
      ∑ i,a i*(∑ v,markedWheelSpokeLoad (T i) j v u) := by
  simp_rw [markedWheelSpokeLoad_combination]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
end
end Oberwolfach
