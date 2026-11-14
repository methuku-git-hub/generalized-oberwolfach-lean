module

public import Oberwolfach.DegreeCutMatchingDeletion

@[expose] public section

/-! Nonempty large cuts after deleting a relation of bounded row degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem large_cut_after_bounded_deletion {X Y : Type*} [Fintype X] [Fintype Y]
    (E J : X → Y → Prop) (S : Finset X) (T : Finset Y)
    (a B lam : ℝ) (ha : 0<a) (hlam : 0<lam) (hmargin : B<lam*a)
    (hS : a≤(S.card:ℝ)) (hT : a≤(T.card:ℝ))
    (hj : ∀ x, ((Finset.univ.filter (J x)).card:ℝ)≤B)
    (hcut : lam*S.card*T.card ≤
      (bipartiteMatrixCut (fun x y => if E x y then 1 else 0) S T : ℝ)) :
    ∃ x∈S, ∃ y∈T, E x y ∧ ¬J x y := by
  classical
  by_contra hn
  have hinc : ∀ x∈S, ∀ y∈T, E x y → J x y := by
    intro x hx y hy he
    by_contra hj
    exact hn ⟨x,hx,y,hy,he,hj⟩
  have hupper : (bipartiteMatrixCut (fun x y => if E x y then 1 else 0) S T : ℝ)
      ≤ (S.card:ℝ)*B := by
    simp only [bipartiteMatrixCut,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    calc
      _ ≤ ∑ _x∈S,B := by
        apply Finset.sum_le_sum
        intro x hx
        calc
          _ ≤ ∑ y∈T, if J x y then (1:ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro y hy
            by_cases he : E x y
            · simp [he,hinc x hx y hy he]
            · simp only [he,ite_false]; positivity
          _ ≤ ∑ y, if J x y then (1:ℝ) else 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
              (by intro y hy hyt; positivity)
          _ ≤ B := by simpa using hj x
      _ = _ := by simp
  have hp : (0:ℝ)<S.card := ha.trans_le hS
  have hs := mul_lt_mul_of_pos_left
    (hmargin.trans_le (mul_le_mul_of_nonneg_left hT hlam.le)) hp
  nlinarith only [hupper,hcut,hs]

theorem degree_after_bounded_relation_deletion {Y : Type*} [Fintype Y]
    (E J : Y → Prop) (d B : ℝ)
    (he : d≤((Finset.univ.filter E).card:ℝ))
    (hj : ((Finset.univ.filter J).card:ℝ)≤B) :
    d-B ≤ ((Finset.univ.filter (fun y => E y ∧ ¬J y)).card:ℝ) := by
  have hh := filter_card_le_kept_add_deleted E J
  have hr : ((Finset.univ.filter E).card:ℝ) ≤
      (Finset.univ.filter (fun y => E y ∧ ¬J y)).card + (Finset.univ.filter J).card := by
    exact_mod_cast hh
  linarith

end Oberwolfach
