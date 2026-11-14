module

public import Oberwolfach.SuccessorSequenceWeights

@[expose] public section

/-! Positional bounds in the coordinates used for marked parent wheels.
The last position closes through the prescribed permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] {m b : ℕ} {P : SimpleGraph V} {π : Equiv.Perm V}
  {D τ A B : ℝ} {weight : (Fin (m+1)→V)→ℝ}

theorem cycleNext_castSucc (i : Fin m) : cycleNext i.castSucc=i.succ := by
  apply Fin.ext
  simp only [cycleNext,Fin.val_castSucc,Fin.val_succ]
  exact Nat.mod_eq_of_lt (by omega)

theorem cycleNext_last : cycleNext (Fin.last m)=0 := by
  apply Fin.ext
  simp [cycleNext]

theorem successor_weight_zero_of_not_separated
    (hw : SuccessorSequenceWeightConditions P π b D τ A B weight)
    (C : Fin (m+1)→V) (hC : ¬PermutationSeparated π b C) : weight C=0 := by
  by_contra h
  exact hC (hw.support C (lt_of_le_of_ne (hw.nonneg C) (Ne.symm h))).2

theorem successor_weight_parent_edges
    (hw : SuccessorSequenceWeightConditions P π b D τ A B weight)
    (C : Fin (m+1)→V) (hC : weight C≠0) :
    (∀ i : Fin m,P.Adj (C i.castSucc) (C i.succ)) ∧
      P.Adj (C (Fin.last m)) (π (C 0)) := by
  have hv := (hw.support C (lt_of_le_of_ne (hw.nonneg C) (Ne.symm hC))).1
  refine ⟨fun i=>?_,?_⟩
  · have hi : i.val+1≠m+1 := by omega
    simpa only [SuccessorSequenceValid,Fin.val_castSucc,hi,ite_false,cycleNext_castSucc] using hv i.castSucc
  · simpa only [Fin.val_last,ite_true,cycleNext_last] using hv (Fin.last m)

theorem successor_marked_edge_mass
    (hw : SuccessorSequenceWeightConditions P π b D τ A B weight)
    (x y : V) (hsep : ¬PermutationClose π b x y) (hP : P.Adj x (π y)) :
    1-τ≤(∑ C,if C (Fin.last m)=x ∧ C 0=y then weight C else 0) ∧
      (∑ C,if C (Fin.last m)=x ∧ C 0=y then weight C else 0)≤1 := by
  simpa only [Fin.val_last,ite_true,cycleNext_last] using hw.edges (Fin.last m) x y hsep (by simpa using hP)

theorem successor_ordinary_edge_mass
    (hw : SuccessorSequenceWeightConditions P π b D τ A B weight)
    (x y : V) (hsep : ¬PermutationClose π b x y) (hP : P.Adj x y) :
    (m:ℝ)*(1-τ)≤(∑ i : Fin m,∑ C,if C i.castSucc=x ∧ C i.succ=y then weight C else 0) ∧
      (∑ i : Fin m,∑ C,if C i.castSucc=x ∧ C i.succ=y then weight C else 0)≤m := by
  have hi (i : Fin m) := hw.edges i.castSucc x y hsep (by simpa only [Fin.val_castSucc,show i.val+1≠m+1 by omega,ite_false] using hP)
  simp only [cycleNext_castSucc] at hi
  constructor
  · convert Finset.sum_le_sum (fun (i : Fin m) (_ : i∈Finset.univ)=> (hi i).1) using 1 <;> simp <;> ring
  · convert Finset.sum_le_sum (fun (i : Fin m) (_ : i∈Finset.univ)=> (hi i).2) using 1 <;> simp <;> ring

theorem successor_typed_vertex_mass
    (hw : SuccessorSequenceWeightConditions P π b D τ A B weight)
    (j : Bool) (v : V) :
    (if j then 1 else (m:ℝ))*((1-τ)*D)≤
      (∑ i : Fin (m+1),if decide (i=0)=j then (∑ C,if C i=v then weight C else 0) else 0) ∧
    (∑ i : Fin (m+1),if decide (i=0)=j then (∑ C,if C i=v then weight C else 0) else 0)≤
      (if j then 1 else (m:ℝ))*D := by
  have hi (i : Fin (m+1)) := hw.positions i v
  cases j
  · simp only [Bool.false_eq_true,ite_false]
    rw [Fin.sum_univ_succ]
    simp only [decide_true,Bool.true_eq_false,ite_false,Fin.succ_ne_zero,decide_false,ite_true,zero_add]
    constructor
    · convert Finset.sum_le_sum (fun (i : Fin m) (_ : i∈Finset.univ)=> (hi i.succ).1) using 1 <;> simp <;> ring
    · convert Finset.sum_le_sum (fun (i : Fin m) (_ : i∈Finset.univ)=> (hi i.succ).2) using 1 <;> simp <;> ring
  · simp only [ite_true,one_mul]
    rw [Fin.sum_univ_succ]
    simpa using hi 0

end Oberwolfach
