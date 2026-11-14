module

public import Oberwolfach.RealFlow
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-! Transportation matrices with prescribed marginals. These are the actual
finite-dimensional domains in the cyclic-partite fixed-point argument. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def transportMatrices {X Y : Type*} [Fintype X] [Fintype Y]
    (m : X → ℝ) (n : Y → ℝ) : Set (X → Y → ℝ) :=
  {Q | (∀ x y, 0 ≤ Q x y) ∧ (∀ x, ∑ y, Q x y = m x) ∧
    (∀ y, ∑ x, Q x y = n y)}

theorem transportMatrices_entry_le {X Y : Type*} [Fintype X] [Fintype Y]
    {m : X → ℝ} {n : Y → ℝ} {Q : X → Y → ℝ}
    (hQ : Q ∈ transportMatrices m n) (x : X) (y : Y) :
    Q x y ≤ m x ∧ Q x y ≤ n y := by
  constructor
  · rw [← hQ.2.1 x]
    exact Finset.single_le_sum (fun z _ => hQ.1 x z) (Finset.mem_univ y)
  · rw [← hQ.2.2 y]
    exact Finset.single_le_sum (fun z _ => hQ.1 z y) (Finset.mem_univ x)

theorem transportMatrices_nonempty {X Y : Type*} [Fintype X] [Fintype Y]
    (m : X → ℝ) (n : Y → ℝ) (B : ℝ)
    (hm : ∀ x, 0 ≤ m x) (hn : ∀ y, 0 ≤ n y)
    (hB : 0 < B) (hms : ∑ x, m x = B) (hns : ∑ y, n y = B) :
    (transportMatrices m n).Nonempty := by
  refine ⟨fun x y => m x * n y / B, ?_, ?_, ?_⟩
  · intro x y
    exact div_nonneg (mul_nonneg (hm x) (hn y)) hB.le
  · intro x
    rw [← Finset.sum_div, ← Finset.mul_sum, hns, mul_div_cancel_right₀ _ hB.ne']
  · intro y
    rw [← Finset.sum_div, ← Finset.sum_mul, hms, mul_div_cancel_left₀ _ hB.ne']

theorem transportMatrices_convex {X Y : Type*} [Fintype X] [Fintype Y]
    (m : X → ℝ) (n : Y → ℝ) :
    Convex ℝ (transportMatrices m n) := by
  intro Q hQ R hR a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact add_nonneg (mul_nonneg ha (hQ.1 x y)) (mul_nonneg hb (hR.1 x y))
  · intro x
    change (∑ y, (a * Q x y + b * R x y)) = m x
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hQ.2.1 x, hR.2.1 x, ← add_mul, hab, one_mul]
  · intro y
    change (∑ x, (a * Q x y + b * R x y)) = n y
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hQ.2.2 y, hR.2.2 y, ← add_mul, hab, one_mul]

theorem transportMatrices_isClosed {X Y : Type*} [Fintype X] [Fintype Y]
    (m : X → ℝ) (n : Y → ℝ) :
    IsClosed (transportMatrices m n) := by
  unfold transportMatrices
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const ((continuous_apply y).comp (continuous_apply x))
  · apply IsClosed.inter
    · exact isClosed_iInter fun x =>
        isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_iInter fun y =>
        isClosed_eq (by fun_prop) continuous_const

theorem transportMatrices_isCompact {X Y : Type*} [Fintype X] [Fintype Y]
    (m : X → ℝ) (n : Y → ℝ) :
    IsCompact (transportMatrices m n) := by
  refine (isCompact_Icc : IsCompact
    (Set.Icc (fun _ : X => fun _ : Y => (0 : ℝ)) (fun x _ => m x))).of_isClosed_subset
    (transportMatrices_isClosed m n) ?_
  intro Q hQ
  exact ⟨hQ.1, fun x y => (transportMatrices_entry_le hQ x y).1⟩

def composeTransport {X Y Z : Type*} [Fintype Y]
    (m : Y → ℝ) (K : X → Y → ℝ) (L : Y → Z → ℝ) : X → Z → ℝ :=
  fun x z => ∑ y, K x y * L y z / m y

theorem composeTransport_mem {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    {a : X → ℝ} {m : Y → ℝ} {b : Z → ℝ}
    {K : X → Y → ℝ} {L : Y → Z → ℝ}
    (hK : K ∈ transportMatrices a m) (hL : L ∈ transportMatrices m b)
    (hm : ∀ y, 0 < m y) :
    composeTransport m K L ∈ transportMatrices a b := by
  refine ⟨?_, ?_, ?_⟩
  · intro x z
    exact Finset.sum_nonneg fun y _ =>
      div_nonneg (mul_nonneg (hK.1 x y) (hL.1 y z)) (hm y).le
  · intro x
    unfold composeTransport
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_div, ← Finset.mul_sum, hL.2.1,
      mul_div_cancel_right₀ _ (hm _).ne']
    exact hK.2.1 x
  · intro z
    unfold composeTransport
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_div, ← Finset.sum_mul, hK.2.2,
      mul_div_cancel_left₀ _ (hm _).ne']
    exact hL.2.2 z

theorem composeTransport_assoc {W X Y Z : Type*} [Fintype X] [Fintype Y]
    (m : X → ℝ) (n : Y → ℝ)
    (K : W → X → ℝ) (L : X → Y → ℝ) (R : Y → Z → ℝ) :
    composeTransport n (composeTransport m K L) R =
      composeTransport m K (composeTransport n L R) := by
  funext w z
  unfold composeTransport
  simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem composeTransport_continuous {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (m : Y → ℝ) :
    Continuous (fun KL : (X → Y → ℝ) × (Y → Z → ℝ) =>
      composeTransport m KL.1 KL.2) := by
  unfold composeTransport
  fun_prop

end Oberwolfach
