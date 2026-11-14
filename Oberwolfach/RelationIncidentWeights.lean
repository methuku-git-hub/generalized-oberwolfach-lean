module

public import Oberwolfach.BipartiteIntersectionEstimates

@[expose] public section

/-! Summing the cost of changed edges using their actual row and column
degrees. These deterministic inequalities include edges incident with fixed
roots and do not involve probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem relation_separable_weight_bound {A B : Type*} [Fintype A] [Fintype B]
    (D : A → B → Prop) (d : ℝ)
    (hout : ∀ x,(∑ y,bipAdj D x y)≤d) (hin : ∀ y,(∑ x,bipAdj D x y)≤d)
    (a : A → ℝ) (b : B → ℝ) (c : ℝ)
    (ha : ∀ x,0≤a x) (hb : ∀ y,0≤b y) (hc : 0≤c) :
    (∑ x,∑ y,bipAdj D x y*(a x+b y+c))≤
      d*((∑ x,a x)+(∑ y,b y)+(Fintype.card A:ℝ)*c) := by
  have h1 : (∑ x,∑ y,bipAdj D x y*a x)≤d*∑ x,a x := by
    simp_rw [← Finset.sum_mul]
    calc
      _ ≤ ∑ x,d*a x := Finset.sum_le_sum (fun x _=>mul_le_mul_of_nonneg_right (hout x) (ha x))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have h2 : (∑ x,∑ y,bipAdj D x y*b y)≤d*∑ y,b y := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    calc
      _ ≤ ∑ y,d*b y := Finset.sum_le_sum (fun y _=>mul_le_mul_of_nonneg_right (hin y) (hb y))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have h3 : (∑ x,∑ y,bipAdj D x y*c)≤(Fintype.card A:ℝ)*d*c := by
    calc
      _ = ∑ x,(∑ y,bipAdj D x y)*c := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_mul]
      _ ≤ ∑ _x : A,d*c := Finset.sum_le_sum (fun x _=>mul_le_mul_of_nonneg_right (hout x) hc)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
  simp only [mul_add,Finset.sum_add_distrib]
  nlinarith

theorem relation_root_incident_cost {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (D : A → B → Prop) (d : ℝ)
    (hout : ∀ x,(∑ y,bipAdj D x y)≤d) (hin : ∀ y,(∑ x,bipAdj D x y)≤d)
    (S : Finset A) (T : Finset B) (M N : ℝ) (hM : 0≤M) (hN : 0≤N) :
    (∑ x,∑ y,if D x y then (if x∈S ∨ y∈T then M else N) else 0)≤
      d*((S.card+T.card:ℝ)*M+(Fintype.card A:ℝ)*N) := by
  let a (x : A) : ℝ := if x∈S then M else 0
  let b (y : B) : ℝ := if y∈T then M else 0
  have hb := relation_separable_weight_bound D d hout hin a b N
    (fun x=>by dsimp only [a];split_ifs <;> positivity)
    (fun y=>by dsimp only [b];split_ifs <;> positivity) hN
  have hs : (∑ x,a x)=(S.card:ℝ)*M := by
    dsimp only [a]
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun x=>x∈S)=S := by ext;simp
    rw [he,Finset.sum_const,nsmul_eq_mul]
  have ht : (∑ y,b y)=(T.card:ℝ)*M := by
    dsimp only [b]
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun y=>y∈T)=T := by ext;simp
    rw [he,Finset.sum_const,nsmul_eq_mul]
  rw [hs,ht] at hb
  calc
    _ ≤ ∑ x,∑ y,bipAdj D x y*(a x+b y+N) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      dsimp only [a,b,bipAdj]
      split_ifs <;> simp_all <;> linarith
    _ ≤ _ := by convert hb using 1 <;> ring

end Oberwolfach
