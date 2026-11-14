module

public import Oberwolfach.CapacityPathWeights

@[expose] public section

/-! Subtracting a path reserve preserves internal balance. The remaining
capacities have a continuous exact path weighting with positive degrees. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def residualIntervalCapacity {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (ρ : (Fin (k+1) → X) → ℝ) (j : Fin k) (x y : X) : ℝ :=
  a j x y-pathEdgeLoad ρ j x y

def residualIntervalDegree {X : Type*} [Fintype X] {k : ℕ}
    (d : Fin (k+1) → X → ℝ) (ρ : (Fin (k+1) → X) → ℝ) (j : Fin (k+1)) (x : X) : ℝ :=
  d j x-pathVertexLoad ρ j x

theorem pathVertexLoad_nonneg {X : Type*} [Fintype X] {k : ℕ}
    (ρ : (Fin (k+1) → X) → ℝ) (hρ : ∀ p, 0 ≤ ρ p)
    (j : Fin (k+1)) (x : X) : 0 ≤ pathVertexLoad ρ j x := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs <;> first | exact hρ p | exact le_refl _

theorem residualIntervalDegree_bounds {X : Type*} [Fintype X] {k : ℕ} (hk : 0 < k)
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ρ : (Fin (k+1) → X) → ℝ) (hρ : ∀ p, 0 ≤ ρ p)
    (hd : ∀ j x, 0 < d j x)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x)
    (hcol : ∀ j y, ∑ x, a j x y=d j.succ y)
    (hreserve : ∀ j x y, pathEdgeLoad ρ j x y ≤ (11/27)*a j x y) :
    ∀ j x, d j x/2 ≤ residualIntervalDegree d ρ j x ∧ residualIntervalDegree d ρ j x ≤ d j x := by
  intro j x
  have hv : pathVertexLoad ρ j x ≤ (11/27)*d j x := by
    by_cases hj : j.val < k
    · let e : Fin k := ⟨j.val,hj⟩
      have he : e.castSucc=j := by ext; rfl
      have hh := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hreserve e x y)
      rw [pathEdgeLoad_row,← Finset.mul_sum,hrow,he] at hh
      exact hh
    · let e : Fin k := ⟨k-1,by omega⟩
      have he : e.succ=j := by ext; dsimp [e]; omega
      have hh := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hreserve e y x)
      rw [pathEdgeLoad_column,← Finset.mul_sum,hcol,he] at hh
      exact hh
  have h0 := pathVertexLoad_nonneg ρ hρ j x
  have h1 := hd j x
  unfold residualIntervalDegree
  constructor <;> nlinarith

theorem residualIntervalCapacity_row {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ρ : (Fin (k+1) → X) → ℝ)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x) :
    ∀ j x, (∑ y, residualIntervalCapacity a ρ j x y)=residualIntervalDegree d ρ j.castSucc x := by
  intro j x
  simp only [residualIntervalCapacity,Finset.sum_sub_distrib,pathEdgeLoad_row,hrow,residualIntervalDegree]

theorem residualIntervalCapacity_column {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ρ : (Fin (k+1) → X) → ℝ)
    (hcol : ∀ j y, ∑ x, a j x y=d j.succ y) :
    ∀ j y, (∑ x, residualIntervalCapacity a ρ j x y)=residualIntervalDegree d ρ j.succ y := by
  intro j y
  simp only [residualIntervalCapacity,Finset.sum_sub_distrib,pathEdgeLoad_column,hcol,residualIntervalDegree]

def halfResidualPathWeight {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ρ : (Fin (k+1) → X) → ℝ) (p : Fin (k+1) → X) : ℝ :=
  capacityPathWeight (residualIntervalCapacity a ρ) (residualIntervalDegree d ρ) p/2

theorem pathEdgeLoad_div {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (c : ℝ) (j : Fin k) (x y : X) :
    pathEdgeLoad (fun p => w p/c) j x y=pathEdgeLoad w j x y/c := by
  unfold pathEdgeLoad
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

theorem pathVertexLoad_div {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (c : ℝ) (j : Fin (k+1)) (x : X) :
    pathVertexLoad (fun p => w p/c) j x=pathVertexLoad w j x/c := by
  unfold pathVertexLoad
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

theorem halfResidualPathWeight_properties {X : Type*} [Fintype X] {k : ℕ} (hk : 0 < k)
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ρ : (Fin (k+1) → X) → ℝ) (Q : X → X → ℝ)
    (ha : ∀ j x y, 0 ≤ a j x y) (hd : ∀ j x, 0 < d j x)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x)
    (hcol : ∀ j y, ∑ x, a j x y=d j.succ y)
    (hρ : ∀ p, 0 ≤ ρ p)
    (hreserve : ∀ j x y, pathEdgeLoad ρ j x y ≤ (11/27)*a j x y)
    (hends : ∀ x z, (∑ p, if p 0=x ∧ p (Fin.last k)=z then ρ p else 0)=Q x z)
    (hQ : Q ∈ transportMatrices (fun x => d 0 x/3) (fun z => d (Fin.last k) z/3)) :
    (∀ p, 0 ≤ halfResidualPathWeight a d ρ p) ∧
    (∀ j x y, pathEdgeLoad (halfResidualPathWeight a d ρ) j x y=
      (a j x y-pathEdgeLoad ρ j x y)/2) ∧
    (∀ x, pathVertexLoad (halfResidualPathWeight a d ρ) 0 x=d 0 x/3) ∧
    (∀ z, pathVertexLoad (halfResidualPathWeight a d ρ) (Fin.last k) z=d (Fin.last k) z/3) := by
  have hra : ∀ j x y, 0 ≤ residualIntervalCapacity a ρ j x y := by
    intro j x y
    exact (div_nonneg (ha j x y) (by norm_num)).trans
      ((residual_path_capacity_bounds a ρ ha hρ hreserve j x y).1)
  have hrd : ∀ j x, 0 < residualIntervalDegree d ρ j x := by
    intro j x
    exact (half_pos (hd j x)).trans_le ((residualIntervalDegree_bounds hk a d ρ hρ hd hrow hcol hreserve j x).1)
  have hrrow := residualIntervalCapacity_row a d ρ hrow
  have hrcol := residualIntervalCapacity_column a d ρ hcol
  have hb := capacityPathWeight_boundary _ _ hra hrd hrrow hrcol
  have hρends := pathVertexLoad_endpoints ρ Q hends
  refine ⟨?_,?_,?_,?_⟩
  · intro p
    exact div_nonneg (capacityPathWeight_nonneg _ _ hra hrd hrrow p) (by norm_num)
  · intro j x y
    change pathEdgeLoad (fun p => capacityPathWeight (residualIntervalCapacity a ρ)
      (residualIntervalDegree d ρ) p/2) j x y=_
    rw [pathEdgeLoad_div,capacityPathWeight_edge _ _ hra hrd hrrow hrcol]
    rfl
  · intro x
    change pathVertexLoad (fun p => capacityPathWeight (residualIntervalCapacity a ρ)
      (residualIntervalDegree d ρ) p/2) 0 x=_
    rw [pathVertexLoad_div,hb.1]
    unfold residualIntervalDegree
    rw [hρends.1,hQ.2.1]
    ring
  · intro z
    change pathVertexLoad (fun p => capacityPathWeight (residualIntervalCapacity a ρ)
      (residualIntervalDegree d ρ) p/2) (Fin.last k) z=_
    rw [pathVertexLoad_div,hb.2]
    unfold residualIntervalDegree
    rw [hρends.2,hQ.2.2]
    ring

end Oberwolfach
