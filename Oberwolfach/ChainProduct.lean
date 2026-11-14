module

public import Oberwolfach.TransportChainJoint

@[expose] public section

/-! A pointwise product formula for the boundary chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem chainJoint_product_with_last {I X : Type*}
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (i : I) (j : ℕ) (w : Fin (j + 1) → X) :
    chainJoint m K s i j w =
      m (s^[j] i) (w (Fin.last j)) *
        ∏ t : Fin j, K (s^[t.val] i) (w t.castSucc) (w t.succ) /
          m (s^[t.val + 1] i) (w t.succ) := by
  induction j generalizing i with
  | zero => simp [chainJoint]
  | succ j ih =>
    change K i (w 0) (w 1) / m (s i) (w 1) *
      chainJoint m K s (s i) j (Fin.tail w) = _
    rw [ih, Fin.prod_univ_succ]
    simp only [Fin.val_zero, Function.iterate_zero_apply, Nat.zero_add,
      Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Fin.val_succ, Function.iterate_succ_apply, Fin.tail, Fin.succ_castSucc, Fin.succ_last]
    ring

theorem chainJoint_product {I X : Type*}
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 < m i x)
    (i : I) (j : ℕ) (w : Fin (j + 2) → X) :
    chainJoint m K s i (j + 1) w =
      (∏ t : Fin (j + 1), K (s^[t.val] i) (w t.castSucc) (w t.succ)) /
      ∏ t : Fin j, m (s^[t.val + 1] i) (w t.succ.castSucc) := by
  rw [chainJoint_product_with_last, Finset.prod_div_distrib]
  have hden :
      (∏ t : Fin (j + 1), m (s^[t.val + 1] i) (w t.succ)) =
        (∏ t : Fin j, m (s^[t.val + 1] i) (w t.succ.castSucc)) *
          m (s^[j + 1] i) (w (Fin.last (j + 1))) := by
    rw [Fin.prod_univ_castSucc]
    rfl
  rw [hden]
  have hlast := (hm (s^[j + 1] i) (w (Fin.last (j + 1)))).ne'
  field_simp

end Oberwolfach
