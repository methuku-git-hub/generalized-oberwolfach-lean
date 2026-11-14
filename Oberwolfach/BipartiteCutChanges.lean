module

public import Oberwolfach.BipartiteQuadraticCut
public import Oberwolfach.FiniteConjunctionChanges

@[expose] public section

/-! Cut changes under insertions and deletions, measured by the actual
symmetric difference in each row and column. No sampling density enters
the loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem bipartite_cut_change_sum (P Q : X→Y→Prop) (S : Finset X) (T : Finset Y) :
    |(bipartiteMatrixCut (fun x y=>if Q x y then 1 else 0) S T:ℝ)-
      (bipartiteMatrixCut (fun x y=>if P x y then 1 else 0) S T:ℝ)|≤
    ∑ x∈S,∑ y∈T,if ¬(P x y ↔ Q x y) then (1:ℝ) else 0 := by
  simp only [bipartiteMatrixCut,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro y hy
  by_cases hp : P x y <;> by_cases hq : Q x y <;> simp [hp,hq]

theorem bipartite_cut_change_degrees (P Q : X→Y→Prop) (ζ : ℝ) (hζ : 0≤ζ)
    (hrow : ∀ x,(∑ y,if ¬(P x y↔Q x y) then (1:ℝ) else 0)≤ζ*Fintype.card Y)
    (hcol : ∀ y,(∑ x,if ¬(P x y↔Q x y) then (1:ℝ) else 0)≤ζ*Fintype.card X)
    (S : Finset X) (T : Finset Y) :
    |(bipartiteMatrixCut (fun x y=>if Q x y then 1 else 0) S T:ℝ)-
      (bipartiteMatrixCut (fun x y=>if P x y then 1 else 0) S T:ℝ)|≤
      ζ*min ((Fintype.card Y:ℝ)*S.card) ((Fintype.card X:ℝ)*T.card) := by
  apply (bipartite_cut_change_sum P Q S T).trans
  rw [mul_min_of_nonneg _ _ hζ]
  apply le_min
  · calc
      _ ≤ ∑ _x∈S,ζ*Fintype.card Y := by
        apply Finset.sum_le_sum
        intro x hx
        apply le_trans _ (hrow x)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
          (by intro y hy hn;split_ifs <;> norm_num)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul];ring
  · rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _y∈T,ζ*Fintype.card X := by
        apply Finset.sum_le_sum
        intro y hy
        apply le_trans _ (hcol y)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (by intro x hx hn;split_ifs <;> norm_num)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul];ring

theorem bipartite_cut_lower_after_changes (P Q : X→Y→Prop) (ζ : ℝ) (hζ : 0≤ζ)
    (hrow : ∀ x,(∑ y,if ¬(P x y↔Q x y) then (1:ℝ) else 0)≤ζ*Fintype.card Y)
    (hcol : ∀ y,(∑ x,if ¬(P x y↔Q x y) then (1:ℝ) else 0)≤ζ*Fintype.card X)
    (c : ℝ) (S : Finset X) (T : Finset Y)
    (hc : c*min ((Fintype.card Y:ℝ)*S.card) ((Fintype.card X:ℝ)*T.card)≤
      (bipartiteMatrixCut (fun x y=>if P x y then 1 else 0) S T:ℝ)) :
    (c-ζ)*min ((Fintype.card Y:ℝ)*S.card) ((Fintype.card X:ℝ)*T.card)≤
      (bipartiteMatrixCut (fun x y=>if Q x y then 1 else 0) S T:ℝ) := by
  have hh := (abs_le.mp (bipartite_cut_change_degrees P Q ζ hζ hrow hcol S T)).1
  nlinarith only [hh,hc]

end Oberwolfach
