module

public import Oberwolfach.TransportChainJoint
public import Oberwolfach.CyclicCoordinates

@[expose] public section

/-! Boundary joint weights obtained by omitting one cyclic interface. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def cyclicBoundaryPair {k : ℕ} {X : Type*} (c i : Fin (k + 2))
    (w : Fin (k + 2) → X) : X × X :=
  (w ((cyclicChainOrder c).symm i),
    w ((cyclicChainOrder c).symm (finRotate (k + 2) i)))

theorem cyclicBoundaryPair_cut {k : ℕ} {X : Type*}
    (c : Fin (k + 2)) (w : Fin (k + 2) → X) :
    cyclicBoundaryPair c c w = (w (Fin.last (k + 1)), w 0) := by
  have hlast : (cyclicChainOrder c).symm c = Fin.last (k + 1) := by
    apply (cyclicChainOrder c).injective
    rw [Equiv.apply_symm_apply, cyclicChainOrder_last]
  have hfirst : (cyclicChainOrder c).symm (finRotate (k + 2) c) = 0 := by
    apply (cyclicChainOrder c).injective
    rw [Equiv.apply_symm_apply, cyclicChainOrder_zero]
  simp only [cyclicBoundaryPair, hlast, hfirst]

theorem complementaryBoundaryJoint_marginal {k : ℕ} {X : Type*} [Fintype X]
    (m : Fin (k + 2) → X → ℝ) (K : Fin (k + 2) → X → X → ℝ)
    (hm : ∀ i x, 0 < m i x)
    (hK : ∀ i, K i ∈ transportMatrices (m i) (m (finRotate (k + 2) i)))
    (c : Fin (k + 2)) (Q : X → X → ℝ)
    (hQ : ∀ x z, Q x z =
      walkTransport m K (finRotate (k + 2)) (finRotate (k + 2) c) (k + 1) z x)
    (i : Fin (k + 2)) (x z : X) :
    (∑ w : Fin (k + 2) → X,
      if cyclicBoundaryPair c i w = (x, z) then
        chainJoint m K (finRotate (k + 2)) (finRotate (k + 2) c) (k + 1) w else 0) =
      if i = c then Q x z else K i x z := by
  by_cases hi : i = c
  · subst i
    simp only [ite_true, cyclicBoundaryPair_cut, Prod.mk.injEq]
    have hh := chainJoint_endpoint_marginal m K (finRotate (k + 2))
      (finRotate (k + 2) c) (k + 1) z x
    rw [hQ]
    simpa only [and_comm] using hh
  · rw [ite_eq_right hi]
    obtain ⟨e, he0, he1, hei⟩ := cyclicChainOrder_positions c i hi
    simp only [cyclicBoundaryPair, he0, he1, Prod.mk.injEq]
    simpa only [hei] using chainJoint_pair_marginal m K (finRotate (k + 2)) hm hK
      (finRotate (k + 2) c) (k + 1) e x z

theorem cyclicBoundaryPair_consistent {k : ℕ} {X : Type*}
    (c i : Fin (k + 2)) (w : Fin (k + 2) → X) :
    (cyclicBoundaryPair c i w).2 =
      (cyclicBoundaryPair c (finRotate (k + 2) i) w).1 := rfl

end Oberwolfach
