module

public import Oberwolfach.DirectedTransversalCycleWeights

@[expose] public section

/-! A supported cycle weighting extended by zero to the fixed vertex-sequence
space. This keeps a common ambient family when capacities vary. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def cycleWeightExtend {c : ℕ} {V : Type*} (a : Fin c → V → V → ℝ)
    (w : DirectedTransversalCycle a → ℝ) (v : Fin c → V) : ℝ :=
  if hv : ∀ i,0<a i (v i) (v (finRotate c i)) then w ⟨v,hv⟩ else 0

@[simp] theorem cycleWeightExtend_on_support {c : ℕ} {V : Type*}
    (a : Fin c → V → V → ℝ) (w : DirectedTransversalCycle a → ℝ)
    (v : DirectedTransversalCycle a) : cycleWeightExtend a w v.val=w v := by
  simp only [cycleWeightExtend,dif_pos v.property]

theorem cycleWeightExtend_nonneg {c : ℕ} {V : Type*}
    (a : Fin c → V → V → ℝ) (w : DirectedTransversalCycle a → ℝ)
    (hw : ∀ v,0≤w v) (v : Fin c → V) : 0≤cycleWeightExtend a w v := by
  unfold cycleWeightExtend
  split_ifs with h
  · exact hw _
  · exact le_rfl

theorem cycleWeightExtend_upper {c : ℕ} {V : Type*}
    (a : Fin c → V → V → ℝ) (w : DirectedTransversalCycle a → ℝ)
    (C : ℝ) (hC : 0≤C) (hw : ∀ v,w v≤C) (v : Fin c → V) : cycleWeightExtend a w v≤C := by
  unfold cycleWeightExtend
  split_ifs with h
  · exact hw _
  · exact hC

theorem cycleWeightExtend_edge {c : ℕ} {V : Type*} [Fintype V]
    (a : Fin c → V → V → ℝ) (w : DirectedTransversalCycle a → ℝ)
    (i : Fin c) (x y : V) :
    (∑ v,if v i=x ∧ v (finRotate c i)=y then cycleWeightExtend a w v else 0)=
      ∑ v : DirectedTransversalCycle a,if v.val i=x ∧ v.val (finRotate c i)=y then w v else 0 := by
  classical
  let S : Set (Fin c → V) := {v | ∀ j,0<a j (v j) (v (finRotate c j))}
  exact Finset.sum_congr_set S
    (fun v => if v i=x ∧ v (finRotate c i)=y then cycleWeightExtend a w v else 0)
    (fun v : S => if v.val i=x ∧ v.val (finRotate c i)=y then w v else 0)
    (by
      intro v hv
      change ∀ j,0<a j (v j) (v (finRotate c j)) at hv
      simp only [cycleWeightExtend,dif_pos hv])
    (by
      intro v hv
      change ¬∀ j,0<a j (v j) (v (finRotate c j)) at hv
      simp only [cycleWeightExtend,dif_neg hv,ite_self])

end Oberwolfach
