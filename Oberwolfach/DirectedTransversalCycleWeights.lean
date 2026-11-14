module

public import Oberwolfach.IntervalCycleWeightTransfer

@[expose] public section

/-! Directed transversal cycles are represented canonically by their vertex in
each labelled class. The edge at interface i goes from class i to its successor. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev DirectedTransversalCycle {c : ℕ} {X : Type*} (a : Fin c → X → X → ℝ) :=
  {v : Fin c → X // ∀ i,0<a i (v i) (v (finRotate c i))}

theorem directed_transversal_weight_restriction {c : ℕ} {X : Type*} [Fintype X]
    (a : Fin c → X → X → ℝ) (ha : ∀ i x y,0≤a i x y)
    (w : (Fin c → X) → ℝ)
    (hz : ∀ v,(∃ i,a i (v i) (v (finRotate c i))=0) → w v=0)
    (he : ∀ i x y,(∑ v,if v i=x ∧ v (finRotate c i)=y then w v else 0)=a i x y)
    (i : Fin c) (x y : X) :
    (∑ v : DirectedTransversalCycle a,if v.val i=x ∧ v.val (finRotate c i)=y then w v.val else 0)=a i x y := by
  classical
  let S : Set (Fin c → X) := {v | ∀ i,0<a i (v i) (v (finRotate c i))}
  have hh := Finset.sum_congr_set S
    (fun v => if v i=x ∧ v (finRotate c i)=y then w v else 0)
    (fun v : S => if v.val i=x ∧ v.val (finRotate c i)=y then w v.val else 0)
    (fun _ _ => rfl) (by
      intro v hv
      have hnot : ¬∀ i,0<a i (v i) (v (finRotate c i)) := hv
      push Not at hnot
      obtain ⟨j,hj⟩ := hnot
      have hzero := hz v ⟨j,le_antisymm hj (ha _ _ _)⟩
      simp only [hzero,ite_self])
  rw [he] at hh
  exact hh.symm

end Oberwolfach
