module

public import Oberwolfach.TransportChainJoint

@[expose] public section

/-! Edge and vertex marginals of a finite weighted path family. These identities
supply internal balance and both boundary degrees after a path reserve is removed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def pathVertexLoad {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (j : Fin (k+1)) (x : X) : ℝ :=
  ∑ p, if p j=x then w p else 0

def pathEdgeLoad {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (j : Fin k) (x y : X) : ℝ :=
  ∑ p, if p j.castSucc=x ∧ p j.succ=y then w p else 0

theorem pathEdgeLoad_row {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (j : Fin k) (x : X) :
    (∑ y, pathEdgeLoad w j x y) = pathVertexLoad w j.castSucc x := by
  unfold pathEdgeLoad pathVertexLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp [ite_and]

theorem pathEdgeLoad_column {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (j : Fin k) (y : X) :
    (∑ x, pathEdgeLoad w j x y) = pathVertexLoad w j.succ y := by
  unfold pathEdgeLoad pathVertexLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp [ite_and]

theorem pathEdgeLoad_nonneg {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (hw : ∀ p, 0 ≤ w p)
    (j : Fin k) (x y : X) : 0 ≤ pathEdgeLoad w j x y := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs <;> first | exact hw p | exact le_refl _

theorem pathVertexLoad_endpoints {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (Q : X → X → ℝ)
    (hQ : ∀ x z, (∑ p, if p 0=x ∧ p (Fin.last k)=z then w p else 0)=Q x z) :
    (∀ x, pathVertexLoad w 0 x=∑ z, Q x z) ∧
    (∀ z, pathVertexLoad w (Fin.last k) z=∑ x, Q x z) := by
  constructor
  · intro x
    simp_rw [← hQ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simp [ite_and]
  · intro z
    simp_rw [← hQ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simp [ite_and]

theorem pathVertexLoad_total {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (j : Fin (k+1)) :
    (∑ x, pathVertexLoad w j x)=∑ p, w p := by
  unfold pathVertexLoad
  rw [Finset.sum_comm]
  simp

theorem residual_path_capacities_balanced {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (w : (Fin (k+1) → X) → ℝ)
    (j l : Fin k) (hjl : j.succ=l.castSucc)
    (hbal : ∀ y, (∑ x, a j x y)=∑ z, a l y z) :
    ∀ y, (∑ x, (a j x y-pathEdgeLoad w j x y)) =
      ∑ z, (a l y z-pathEdgeLoad w l y z) := by
  intro y
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    pathEdgeLoad_column,pathEdgeLoad_row,hjl,hbal]

theorem residual_path_capacity_bounds {X : Type*} [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (w : (Fin (k+1) → X) → ℝ)
    (ha : ∀ j x y, 0 ≤ a j x y) (hw : ∀ p, 0 ≤ w p)
    (hreserve : ∀ j x y, pathEdgeLoad w j x y ≤ (11/27)*a j x y) :
    ∀ j x y, a j x y/2 ≤ a j x y-pathEdgeLoad w j x y ∧
      a j x y-pathEdgeLoad w j x y ≤ a j x y := by
  intro j x y
  have h0 := pathEdgeLoad_nonneg w hw j x y
  have h1 := hreserve j x y
  have h2 := ha j x y
  constructor <;> nlinarith

end Oberwolfach
