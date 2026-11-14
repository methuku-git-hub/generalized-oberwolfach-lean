module

public import Oberwolfach.CapacityPathProducts
public import Oberwolfach.ResidualPathEndpoints

@[expose] public section

/-! Strict positivity of endpoint matrices follows from an actual supported
path, without assuming positivity of an arbitrary input endpoint matrix. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem positive_transition_path_exists {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (hR : ∀ i, IsTransition (R i))
    (i k : ℕ) (x z : X) (hT : 0 < transitionWalk R i k x z) :
    ∃ p : Fin (k+1) → X, p 0=x ∧ p (Fin.last k)=z ∧
      ∀ j : Fin k, 0 < R (i+j.val) (p j.castSucc) (p j.succ) := by
  rw [← transitionPathWeight_endpoint_marginal R i k x z] at hT
  have hn (p : Fin (k+1) → X) (_ : p ∈ Finset.univ) :
      0 ≤ (if p 0=x ∧ p (Fin.last k)=z then transitionPathWeight R i k p else 0) := by
    split_ifs
    · exact transitionPathWeight_nonneg R (fun i => (hR i).1) i k p
    · exact le_refl _
  obtain ⟨p,_,hp⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp hT
  split_ifs at hp with he
  · exact ⟨p,he.1,he.2,(transitionPathWeight_pos_iff R (fun i => (hR i).1) i k p).mp hp⟩
  · exact False.elim (lt_irrefl 0 hp)

theorem pathEndpointMatrix_pos_of_path {X : Type*} [Fintype X] {k : ℕ}
    (w : (Fin (k+1) → X) → ℝ) (hw : ∀ p, 0 ≤ w p)
    (x z : X) (p : Fin (k+1) → X) (hp : p 0=x ∧ p (Fin.last k)=z) (hwpos : 0 < w p) :
    0 < pathEndpointMatrix w x z := by
  have hsingle : w p ≤ pathEndpointMatrix w x z := by
    unfold pathEndpointMatrix
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun q => if q 0=x ∧ q (Fin.last k)=z then w q else 0)
      (by intro q _; split_ifs <;> first | exact hw q | exact le_refl _) (Finset.mem_univ p)
    simpa only [if_pos hp] using hh
  exact hwpos.trans_le hsingle

theorem halfResidualPathWeight_pos {X : Type*} [Fintype X] {k : ℕ} (hk : 0 < k)
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ)
    (ρ : (Fin (k+1) → X) → ℝ)
    (ha : ∀ j x y, 0 ≤ a j x y) (hd : ∀ j x, 0 < d j x)
    (hrow : ∀ j x, ∑ y, a j x y=d j.castSucc x)
    (hcol : ∀ j y, ∑ x, a j x y=d j.succ y)
    (hρ : ∀ p, 0 ≤ ρ p)
    (hreserve : ∀ j x y, pathEdgeLoad ρ j x y ≤ (11/27)*a j x y)
    (p : Fin (k+1) → X) (hp : ∀ j, 0 < a j (p j.castSucc) (p j.succ)) :
    0 < halfResidualPathWeight a d ρ p := by
  have hrd : ∀ j x, 0 < residualIntervalDegree d ρ j x := by
    intro j x
    exact (half_pos (hd j x)).trans_le
      ((residualIntervalDegree_bounds hk a d ρ hρ hd hrow hcol hreserve j x).1)
  have hra : ∀ j, 0 < residualIntervalCapacity a ρ j (p j.castSucc) (p j.succ) := by
    intro j
    exact (half_pos (hp j)).trans_le
      ((residual_path_capacity_bounds a ρ ha hρ hreserve j _ _).1)
  exact div_pos (capacityPathWeight_pos _ _ p hrd hra) (by norm_num)

end Oberwolfach
