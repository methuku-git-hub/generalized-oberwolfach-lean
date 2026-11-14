module

public import Oberwolfach.LongCapacityBoundedAssembly
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-! Periodic indexing of cyclic capacities and the common interface mass. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def cyclicIndex (c : ℕ) [NeZero c] (j : ℕ) : Fin c := ⟨j%c,Nat.mod_lt _ (NeZero.pos c)⟩

@[simp] theorem cyclicIndex_fin {c : ℕ} [NeZero c] (i : Fin c) : cyclicIndex c i.val=i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

@[simp] theorem cyclicIndex_zero (c : ℕ) [NeZero c] : cyclicIndex c 0=0 := by
  apply Fin.ext
  exact Nat.zero_mod c

theorem cyclicIndex_succ (c : ℕ) [NeZero c] (j : ℕ) :
    cyclicIndex c (j+1)=finRotate c (cyclicIndex c j) := by
  rw [finRotate_apply]
  apply Fin.ext
  simp only [cyclicIndex,Fin.val_add]
  exact Nat.add_mod j 1 c

@[simp] theorem cyclicIndex_period (c : ℕ) [NeZero c] (j : ℕ) : cyclicIndex c (j+c)=cyclicIndex c j := by
  apply Fin.ext
  simp [cyclicIndex]

def periodicCapacity {c : ℕ} [NeZero c] {X : Type*} (a : Fin c → X → X → ℝ) : ℕ → X → X → ℝ :=
  fun j => a (cyclicIndex c j)

def periodicDegree {c : ℕ} [NeZero c] {X : Type*} (d : Fin c → X → ℝ) : ℕ → X → ℝ :=
  fun j => d (cyclicIndex c j)

theorem balanced_capacity_mass_constant {X : Type*} [Fintype X]
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ)
    (hrow : ∀ i x,∑ y,a i x y=d i x)
    (hcol : ∀ i y,∑ x,a i x y=d (i+1) y) :
    ∀ i,(∑ x,d i x)=∑ x,d 0 x := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    calc
      (∑ y,d (i+1) y) = ∑ y,∑ x,a i x y := by simp only [hcol]
      _ = ∑ x,∑ y,a i x y := Finset.sum_comm
      _ = ∑ x,d i x := by simp only [hrow]
      _ = ∑ x,d 0 x := ih

theorem periodicCapacity_balance {c : ℕ} [NeZero c] {X : Type*} [Fintype X]
    (a : Fin c → X → X → ℝ) (d : Fin c → X → ℝ)
    (hrow : ∀ i x,∑ y,a i x y=d i x)
    (hcol : ∀ i y,∑ x,a i x y=d (finRotate c i) y) :
    (∀ j x,∑ y,periodicCapacity a j x y=periodicDegree d j x) ∧
      (∀ j y,∑ x,periodicCapacity a j x y=periodicDegree d (j+1) y) := by
  constructor
  · intro j x
    exact hrow _ _
  · intro j y
    simp only [periodicCapacity,periodicDegree,cyclicIndex_succ]
    exact hcol _ _

theorem cyclic_capacity_mass_constant {c : ℕ} [NeZero c] {X : Type*} [Fintype X]
    (a : Fin c → X → X → ℝ) (d : Fin c → X → ℝ)
    (hrow : ∀ i x,∑ y,a i x y=d i x)
    (hcol : ∀ i y,∑ x,a i x y=d (finRotate c i) y) (i : Fin c) :
    (∑ x,d i x)=∑ x,d 0 x := by
  obtain ⟨hr,hc⟩ := periodicCapacity_balance a d hrow hcol
  simpa only [periodicDegree,cyclicIndex_fin,cyclicIndex_zero] using
    balanced_capacity_mass_constant (periodicCapacity a) (periodicDegree d) hr hc i.val

def cyclicCapacityTransition {c : ℕ} {X : Type*} (a : Fin c → X → X → ℝ) (d : Fin c → X → ℝ)
    (i : Fin c) (x y : X) : ℝ := a i x y/d i x

theorem transitionWalk_three {X : Type*} [Fintype X] (R : ℕ → X → X → ℝ) (j : ℕ) (x z : X) :
    transitionWalk R j 3 x z=∑ y,∑ w,R j x y*R (j+1) y w*R (j+2) w z := by
  change transitionCompose (R j) (transitionCompose (R (j+1))
    (transitionCompose (R (j+2)) identityTransition)) x z=_
  rw [transitionCompose_identity_right]
  simp [transitionCompose,Finset.mul_sum,mul_assoc]

theorem periodicCapacity_three {c : ℕ} [NeZero c] {X : Type*} [Fintype X]
    (a : Fin c → X → X → ℝ) (d : Fin c → X → ℝ) (j : ℕ) (x z : X) :
    transitionWalk (capacityTransition (periodicCapacity a) (periodicDegree d)) j 3 x z=
      ∑ y,∑ w,cyclicCapacityTransition a d (cyclicIndex c j) x y*
        cyclicCapacityTransition a d (finRotate c (cyclicIndex c j)) y w*
        cyclicCapacityTransition a d (finRotate c (finRotate c (cyclicIndex c j))) w z := by
  rw [transitionWalk_three]
  simp only [capacityTransition,periodicCapacity,periodicDegree,cyclicCapacityTransition,
    show j+2=j+1+1 from rfl,cyclicIndex_succ]

theorem cyclicIndex_mem_image_iff {c : ℕ} [NeZero c] (J : Finset (Fin c)) (j : ℕ) (hj : j<c) :
    cyclicIndex c j∈J ↔ j∈J.image Fin.val := by
  constructor
  · intro h
    exact Finset.mem_image.mpr ⟨cyclicIndex c j,h,Nat.mod_eq_of_lt hj⟩
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    simpa only [cyclicIndex_fin] using hi

end Oberwolfach
