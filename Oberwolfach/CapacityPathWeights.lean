module

public import Oberwolfach.WeightedTransitionPaths

@[expose] public section

/-! Path weights from balanced positive degree distributions on a finite
interval. Transitions outside the interval are identities and are not assigned
any extra balance assumptions. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def finiteIntervalTransition {X : Type*} {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ) (i : ℕ) (x y : X) : ℝ :=
  if hi : i < k then a ⟨i,hi⟩ x y / d ⟨i,by omega⟩ x else identityTransition x y

def intervalDegreeExtend {X : Type*} {k : ℕ}
    (d : Fin (k+1) → X → ℝ) (i : ℕ) : X → ℝ :=
  if hi : i < k+1 then d ⟨i,hi⟩ else d 0

theorem finiteIntervalTransition_isTransition {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ha : ∀ j x y, 0 ≤ a j x y) (hd : ∀ j x, 0 < d j x)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x) :
    ∀ i, IsTransition (finiteIntervalTransition a d i) := by
  intro i
  by_cases hi : i < k
  · constructor
    · intro x y
      simp only [finiteIntervalTransition, dif_pos hi]
      exact div_nonneg (ha _ _ _) (hd _ _).le
    · intro x
      simp only [finiteIntervalTransition,dif_pos hi,← Finset.sum_div,hrow]
      exact div_self (hd _ _).ne'
  · have heq : finiteIntervalTransition a d i=identityTransition := by
      funext x y
      simp only [finiteIntervalTransition,dif_neg hi]
    rw [heq]
    exact identityTransition_isTransition

theorem intervalDegreeExtend_balance {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (hd : ∀ j x, 0 < d j x)
    (hcol : ∀ j y, ∑ x, a j x y=d j.succ y) :
    ∀ i < k, transitionApply (intervalDegreeExtend d i) (finiteIntervalTransition a d i)=
      intervalDegreeExtend d (i+1) := by
  intro i hi
  funext y
  have hi' : i < k+1 := by omega
  have hi'' : i+1 < k+1 := by omega
  simp only [transitionApply,intervalDegreeExtend,dif_pos hi',dif_pos hi'',
    finiteIntervalTransition,dif_pos hi]
  have hcancel (x : X) : d ⟨i,hi'⟩ x*(a ⟨i,hi⟩ x y/d ⟨i,hi'⟩ x)=a ⟨i,hi⟩ x y := by
    field_simp [(hd _ _).ne']
  simp_rw [hcancel]
  exact hcol ⟨i,hi⟩ y

def capacityPathWeight {X : Type*} {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ) : (Fin (k+1) → X) → ℝ :=
  weightedTransitionPath (d 0) (finiteIntervalTransition a d) 0 k

theorem capacityPathWeight_nonneg {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ha : ∀ j x y, 0 ≤ a j x y) (hd : ∀ j x, 0 < d j x)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x) :
    ∀ p, 0 ≤ capacityPathWeight a d p := by
  intro p
  exact mul_nonneg (hd _ _).le (transitionPathWeight_nonneg _
    (fun i => (finiteIntervalTransition_isTransition a d ha hd hrow i).1) 0 k p)

theorem capacityPathWeight_edge {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ha : ∀ j x y, 0 ≤ a j x y) (hd : ∀ j x, 0 < d j x)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x)
    (hcol : ∀ j y, ∑ x, a j x y=d j.succ y)
    (j : Fin k) (x y : X) : pathEdgeLoad (capacityPathWeight a d) j x y=a j x y := by
  unfold capacityPathWeight
  rw [weightedTransitionPath_edge _ _ (finiteIntervalTransition_isTransition a d ha hd hrow)]
  have hbal := transitionWalk_stationary_local (finiteIntervalTransition a d) (intervalDegreeExtend d)
    0 j.val (by
      intro i hi
      simpa only [Nat.zero_add] using intervalDegreeExtend_balance a d hd hcol i (by omega))
  have hzero : intervalDegreeExtend d 0=d 0 := by simp [intervalDegreeExtend]
  rw [hzero,Nat.zero_add] at hbal
  have hdj : intervalDegreeExtend d j.val=d j.castSucc := by
    unfold intervalDegreeExtend
    rw [dif_pos (show j.val < k+1 by omega)]
    rfl
  rw [hbal,hdj]
  simp only [Nat.zero_add,finiteIntervalTransition, dif_pos j.isLt]
  change d j.castSucc x*(a j x y/d j.castSucc x)=a j x y
  field_simp [(hd j.castSucc x).ne']

theorem capacityPathWeight_boundary {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ha : ∀ j x y, 0 ≤ a j x y) (hd : ∀ j x, 0 < d j x)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x)
    (hcol : ∀ j y, ∑ x, a j x y=d j.succ y) :
    (∀ x, pathVertexLoad (capacityPathWeight a d) 0 x=d 0 x) ∧
    (∀ y, pathVertexLoad (capacityPathWeight a d) (Fin.last k) y=d (Fin.last k) y) := by
  constructor
  · intro x
    exact weightedTransitionPath_first _ _ (finiteIntervalTransition_isTransition a d ha hd hrow) _ _ x
  · intro y
    rw [capacityPathWeight,weightedTransitionPath_last]
    have hbal := transitionWalk_stationary_local (finiteIntervalTransition a d) (intervalDegreeExtend d)
      0 k (by
        intro i hi
        simpa only [Nat.zero_add] using intervalDegreeExtend_balance a d hd hcol i hi)
    have hzero : intervalDegreeExtend d 0=d 0 := by simp [intervalDegreeExtend]
    rw [hzero,Nat.zero_add] at hbal
    rw [hbal]
    simp only [intervalDegreeExtend,dif_pos (Nat.lt_succ_self k)]
    rfl

theorem transitionPathWeight_continuous {T X : Type*} [TopologicalSpace T]
    (R : T → ℕ → X → X → ℝ) (hR : ∀ i x y, Continuous (fun z => R z i x y))
    (i k : ℕ) (p : Fin (k+1) → X) : Continuous (fun z => transitionPathWeight (R z) i k p) := by
  induction k generalizing i with
  | zero => exact continuous_const
  | succ k ih => exact (hR i _ _).mul (ih (i+1) (Fin.tail p))

theorem capacityPathWeight_continuous {T X : Type*} [TopologicalSpace T] {k : ℕ}
    (a : T → Fin k → X → X → ℝ) (d : T → Fin (k+1) → X → ℝ)
    (ha : ∀ j x y, Continuous (fun z => a z j x y))
    (hd : ∀ j x, Continuous (fun z => d z j x)) (hdpos : ∀ z j x, 0 < d z j x) :
    Continuous (fun z => capacityPathWeight (a z) (d z)) := by
  apply continuous_pi
  intro p
  apply (hd 0 (p 0)).mul
  apply transitionPathWeight_continuous
  intro i x y
  by_cases hi : i < k
  · simp only [finiteIntervalTransition,dif_pos hi]
    exact (ha _ _ _).div (hd _ _) (fun z => (hdpos z _ _).ne')
  · simp only [finiteIntervalTransition,dif_neg hi]
    exact continuous_const

end Oberwolfach
