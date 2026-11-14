module

public import Oberwolfach.ResidualCapacityPaths

@[expose] public section

/-! The half-residual path construction gives a continuous map into the
transportation polytope with the original prescribed boundary marginals. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def pathEndpointMatrix {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (x z : X) : ℝ :=
  ∑ p, if p 0=x ∧ p (Fin.last k)=z then w p else 0

theorem pathEndpointMatrix_mem {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (d e : X → ℝ)
    (hw : ∀ p, 0 ≤ w p)
    (hfirst : ∀ x, pathVertexLoad w 0 x=d x)
    (hlast : ∀ z, pathVertexLoad w (Fin.last k) z=e z) :
    pathEndpointMatrix w ∈ transportMatrices d e := by
  refine ⟨?_,?_,?_⟩
  · intro x z
    apply Finset.sum_nonneg
    intro p _
    split_ifs <;> first | exact hw p | exact le_refl _
  · intro x
    exact ((pathVertexLoad_endpoints w (pathEndpointMatrix w) (fun _ _ => rfl)).1 x).symm.trans (hfirst x)
  · intro z
    exact ((pathVertexLoad_endpoints w (pathEndpointMatrix w) (fun _ _ => rfl)).2 z).symm.trans (hlast z)

theorem pathVertexLoad_continuous {T X : Type*} [TopologicalSpace T] [Fintype X] {k : ℕ}
    (w : T → (Fin (k+1) → X) → ℝ) (hw : ∀ p, Continuous (fun z => w z p))
    (j : Fin (k+1)) (x : X) : Continuous (fun z => pathVertexLoad (w z) j x) := by
  unfold pathVertexLoad
  apply continuous_finset_sum
  intro p _
  split_ifs <;> first | exact hw p | exact continuous_const

theorem pathEdgeLoad_continuous {T X : Type*} [TopologicalSpace T] [Fintype X] {k : ℕ}
    (w : T → (Fin (k+1) → X) → ℝ) (hw : ∀ p, Continuous (fun z => w z p))
    (j : Fin k) (x y : X) : Continuous (fun z => pathEdgeLoad (w z) j x y) := by
  unfold pathEdgeLoad
  apply continuous_finset_sum
  intro p _
  split_ifs <;> first | exact hw p | exact continuous_const

theorem pathEndpointMatrix_continuous {T X : Type*} [TopologicalSpace T] [Fintype X] {k : ℕ}
    (w : T → (Fin (k+1) → X) → ℝ) (hw : ∀ p, Continuous (fun z => w z p)) :
    Continuous (fun z => pathEndpointMatrix (w z)) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  unfold pathEndpointMatrix
  apply continuous_finset_sum
  intro p _
  split_ifs <;> first | exact hw p | exact continuous_const

theorem halfResidualPathWeight_continuous {T X : Type*} [TopologicalSpace T] [Fintype X] {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ρ : T → (Fin (k+1) → X) → ℝ) (hρ : ∀ p, Continuous (fun z => ρ z p))
    (hdpos : ∀ z j x, 0 < residualIntervalDegree d (ρ z) j x) :
    Continuous (fun z => halfResidualPathWeight a d (ρ z)) := by
  have ha : ∀ j x y, Continuous (fun z => residualIntervalCapacity a (ρ z) j x y) := by
    intro j x y
    exact continuous_const.sub (pathEdgeLoad_continuous ρ hρ j x y)
  have hd : ∀ j x, Continuous (fun z => residualIntervalDegree d (ρ z) j x) := by
    intro j x
    exact continuous_const.sub (pathVertexLoad_continuous ρ hρ j x)
  have hc := capacityPathWeight_continuous (fun z => residualIntervalCapacity a (ρ z))
    (fun z => residualIntervalDegree d (ρ z)) ha hd hdpos
  apply continuous_pi
  intro p
  exact ((continuous_apply p).comp hc).div_const 2

theorem halfResidualEndpoint_mem {X : Type*} [Fintype X] {k : ℕ} (hk : 0 < k)
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ρ : (Fin (k+1) → X) → ℝ) (Q : X → X → ℝ)
    (ha : ∀ j x y, 0 ≤ a j x y) (hd : ∀ j x, 0 < d j x)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x)
    (hcol : ∀ j y, ∑ x, a j x y=d j.succ y)
    (hρ : ∀ p, 0 ≤ ρ p)
    (hreserve : ∀ j x y, pathEdgeLoad ρ j x y ≤ (11/27)*a j x y)
    (hends : pathEndpointMatrix ρ=Q)
    (hQ : Q ∈ transportMatrices (fun x => d 0 x/3) (fun z => d (Fin.last k) z/3)) :
    pathEndpointMatrix (halfResidualPathWeight a d ρ) ∈
      transportMatrices (fun x => d 0 x/3) (fun z => d (Fin.last k) z/3) := by
  obtain ⟨h0,_,hfirst,hlast⟩ := halfResidualPathWeight_properties hk a d ρ Q ha hd hrow hcol hρ hreserve
    (fun x z => congrFun (congrFun hends x) z) hQ
  exact pathEndpointMatrix_mem _ _ _ h0 hfirst hlast

end Oberwolfach
