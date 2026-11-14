module

public import Oberwolfach.SectorProduct
public import Oberwolfach.CyclicPathWeighting

@[expose] public section

/-! The conditional construction cancels every endpoint weight. Only the
residual path weights, the reserved common neighbourhood and the internal
boundary marginals remain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cyclic_sector_formula {k : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    (m : Fin (k + 2) → X → ℝ) (K : Fin (k + 2) → X → X → ℝ)
    (hm : ∀ i x, 0 < m i x) (hK : ∀ i x z, 0 < K i x z)
    (c : Fin (k + 2)) (Q : X → X → ℝ)
    (hQ : ∀ x z, Q x z =
      walkTransport m K (finRotate (k + 2)) (finRotate (k + 2) c) (k + 1) z x)
    (x : Fin (k + 2) → X) (w R : Fin (k + 2) → ℝ) (C : ℝ) (hC : 0 < C)
    (hwc : w c = Q (x c) (x (finRotate (k + 2) c)) / C)
    (hwi : ∀ i, i ≠ c → w i = R i) :
    chainJoint m K (finRotate (k + 2)) (finRotate (k + 2) c) (k + 1)
      (fun j => x (cyclicChainOrder c j)) *
        (∏ i, w i / (if i = c then Q (x i) (x (finRotate (k + 2) i))
          else K i (x i) (x (finRotate (k + 2) i)))) =
      (∏ i ∈ Finset.univ.erase c, R i) /
        (C * ∏ j ∈ (Finset.univ.erase c).erase (finRotate (k + 2) c), m j (x j)) := by
  rw [complementary_chain_product m K hm]
  have hp :
      (∏ i, w i / (if i = c then Q (x i) (x (finRotate (k + 2) i))
        else K i (x i) (x (finRotate (k + 2) i)))) =
      ∏ i, if i = c then
        (Q (x c) (x (finRotate (k + 2) c)) / C) /
          Q (x c) (x (finRotate (k + 2) c))
        else R i / K i (x i) (x (finRotate (k + 2) i)) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i = c
    · subst i
      simp only [ite_true, hwc]
    · simp only [hi, ite_false, hwi i hi]
  rw [hp]
  apply sector_product_cancel c (fun i => K i (x i) (x (finRotate (k + 2) i))) R
  · intro i _
    exact (hK i _ _).ne'
  · rw [hQ]
    exact (walkTransport_pos m K (finRotate (k + 2)) hm hK _ k _ _).ne'
  · exact hC.ne'
  · exact (Finset.prod_pos (fun i _ => hm i (x i))).ne'

end Oberwolfach
