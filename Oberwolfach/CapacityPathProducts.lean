module

public import Oberwolfach.ResidualCapacityPaths

@[expose] public section

/-! Pointwise formulas and support for the capacity-path construction. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem transitionPathWeight_product {X : Type*}
    (R : ℕ → X → X → ℝ) (i k : ℕ) (p : Fin (k+1) → X) :
    transitionPathWeight R i k p=∏ j : Fin k, R (i+j.val) (p j.castSucc) (p j.succ) := by
  induction k generalizing i with
  | zero => simp [transitionPathWeight]
  | succ k ih =>
    rw [transitionPathWeight,ih,Fin.prod_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.castSucc_zero,Fin.succ_zero_eq_one,
      Fin.val_succ,Fin.tail,Fin.succ_castSucc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    congr 1 <;> omega

theorem capacityPathWeight_product {X : Type*} {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ) (p : Fin (k+1) → X) :
    capacityPathWeight a d p=d 0 (p 0)*∏ j : Fin k, a j (p j.castSucc) (p j.succ)/d j.castSucc (p j.castSucc) := by
  unfold capacityPathWeight weightedTransitionPath
  rw [transitionPathWeight_product]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [Nat.zero_add,finiteIntervalTransition,dif_pos j.isLt]
  rfl

theorem capacityPathWeight_pos {X : Type*} {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ) (p : Fin (k+1) → X)
    (hd : ∀ j x, 0 < d j x) (ha : ∀ j, 0 < a j (p j.castSucc) (p j.succ)) :
    0 < capacityPathWeight a d p := by
  rw [capacityPathWeight_product]
  exact mul_pos (hd _ _) (Finset.prod_pos (fun j _ => div_pos (ha j) (hd _ _)))

theorem transitionPathWeight_pos_iff {X : Type*}
    (R : ℕ → X → X → ℝ) (hR : ∀ i x y, 0 ≤ R i x y)
    (i k : ℕ) (p : Fin (k+1) → X) :
    0 < transitionPathWeight R i k p ↔ ∀ j : Fin k, 0 < R (i+j.val) (p j.castSucc) (p j.succ) := by
  rw [transitionPathWeight_product]
  constructor
  · intro hp j
    have hn := Finset.prod_ne_zero_iff.mp hp.ne' j (Finset.mem_univ j)
    exact lt_of_le_of_ne (hR _ _ _) hn.symm
  · intro hp
    exact Finset.prod_pos (fun j _ => hp j)

theorem capacityPathWeight_bounds {X : Type*} {k : ℕ}
    (a : Fin k → X → X → ℝ) (d : Fin (k+1) → X → ℝ) (p : Fin (k+1) → X)
    (a₀ a₁ d₀ d₁ : ℝ) (ha₀ : 0 < a₀) (hd₀ : 0 < d₀)
    (ha : ∀ j, a₀ ≤ a j (p j.castSucc) (p j.succ) ∧ a j (p j.castSucc) (p j.succ) ≤ a₁)
    (hd : ∀ j, d₀ ≤ d j (p j) ∧ d j (p j) ≤ d₁) :
    d₀*(a₀/d₁)^k ≤ capacityPathWeight a d p ∧ capacityPathWeight a d p ≤ d₁*(a₁/d₀)^k := by
  have hd₁ : 0 < d₁ := hd₀.trans_le ((hd 0).1.trans (hd 0).2)
  have hlow (j : Fin k) : a₀/d₁ ≤ a j (p j.castSucc) (p j.succ)/d j.castSucc (p j.castSucc) :=
    div_le_div₀ (ha₀.le.trans (ha j).1) (ha j).1 (hd₀.trans_le (hd _).1) (hd _).2
  have hupp (j : Fin k) : a j (p j.castSucc) (p j.succ)/d j.castSucc (p j.castSucc) ≤ a₁/d₀ :=
    div_le_div₀ (ha₀.le.trans ((ha j).1.trans (ha j).2)) (ha j).2 hd₀ (hd _).1
  rw [capacityPathWeight_product]
  have hlo : (a₀/d₁)^k ≤ ∏ j : Fin k, a j (p j.castSucc) (p j.succ)/d j.castSucc (p j.castSucc) := by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ => (div_pos ha₀ hd₁).le) (fun j _ => hlow j)
  have hup : (∏ j : Fin k, a j (p j.castSucc) (p j.succ)/d j.castSucc (p j.castSucc)) ≤ (a₁/d₀)^k := by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using Finset.prod_le_prod₀ (s := Finset.univ)
      (fun j _ => (div_pos (ha₀.trans_le (ha j).1) (hd₀.trans_le (hd _).1)).le) (fun j _ => hupp j)
  constructor
  · exact mul_le_mul (hd 0).1 hlo (pow_nonneg (div_pos ha₀ hd₁).le _) (hd₀.trans_le (hd 0).1).le
  · exact mul_le_mul (hd 0).2 hup (Finset.prod_nonneg fun j _ =>
      (div_pos (ha₀.trans_le (ha j).1) (hd₀.trans_le (hd _).1)).le) hd₁.le

end Oberwolfach
