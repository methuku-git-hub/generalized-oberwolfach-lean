module

public import Oberwolfach.MarkedSpokeCounts
public import Oberwolfach.BipartiteIntersectionEstimates
public import Oberwolfach.FiniteConfigurationLoss

@[expose] public section

/-! Counting changed binary constraints in tuples, with free or fixed
endpoints. These counts do not require the tuples to be graph embeddings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem tuple_relation_indicator_count (D : V → V → Prop) (i j : I) (hij : i≠j) :
    (∑ z : I → V,if D (z i) (z j) then (1:ℝ) else 0)=
      (∑ x,∑ y,bipAdj D x y)*(Fintype.card V:ℝ)^(Fintype.card I-2) := by
  have expand (z : I → V) : (if D (z i) (z j) then (1:ℝ) else 0)=
      ∑ x,∑ y,if D x y then (if z i=x ∧ z j=y then (1:ℝ) else 0) else 0 := by
    have he (x y : V) : (if D x y then (if z i=x ∧ z j=y then (1:ℝ) else 0) else 0)=
        if x=z i then (if y=z j then bipAdj D x y else 0) else 0 := by
      by_cases hx : x=z i <;> by_cases hy : y=z j <;> by_cases hd : D x y <;> simp_all [bipAdj,eq_comm]
    simp only [he]
    simp [bipAdj]
  simp_rw [expand]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x,∑ y,∑ z : I → V,if D x y then (if z i=x ∧ z j=y then (1:ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ x,∑ y,bipAdj D x y*(Fintype.card V:ℝ)^(Fintype.card I-2) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      by_cases hd : D x y
      · simp only [hd,ite_true,bipAdj,one_mul]
        convert two_position_indicator_total i j hij x y using 1 <;> congr!
      · simp only [hd,ite_false,bipAdj,zero_mul,Finset.sum_const_zero]
    _ = _ := by simp_rw [← Finset.sum_mul]

theorem tuple_relation_deletion_count (D : V → V → Prop) (i j : I) (hij : i≠j)
    (d : ℝ) (hD : ∀ x,(∑ y,bipAdj D x y)≤d) :
    (∑ z : I → V,if D (z i) (z j) then (1:ℝ) else 0)≤
      d*(Fintype.card V:ℝ)^(Fintype.card I-1) := by
  rw [tuple_relation_indicator_count D i j hij]
  have hh : (∑ x,∑ y,bipAdj D x y)≤(Fintype.card V:ℝ)*d := by
    calc
      _ ≤ ∑ _ : V,d := Finset.sum_le_sum (fun x _=>hD x)
      _ = _ := by simp
  have hI : 2≤Fintype.card I := Fintype.one_lt_card_iff.mpr ⟨i,j,hij⟩
  have he : Fintype.card I-1=(Fintype.card I-2)+1 := by omega
  calc
    _ ≤ ((Fintype.card V:ℝ)*d)*(Fintype.card V:ℝ)^(Fintype.card I-2) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by rw [he,pow_succ];ring

theorem tuple_unary_indicator_count (P : V → Prop) (i : I) :
    (∑ z : I → V,if P (z i) then (1:ℝ) else 0)=
      (∑ x,if P x then (1:ℝ) else 0)*(Fintype.card V:ℝ)^(Fintype.card I-1) := by
  have expand (z : I → V) : (if P (z i) then (1:ℝ) else 0)=
      ∑ x,if P x then (if z i=x then (1:ℝ) else 0) else 0 := by
    have he (x : V) : (if P x then (if z i=x then (1:ℝ) else 0) else 0)=
        if x=z i then (if P x then (1:ℝ) else 0) else 0 := by
      by_cases hx : x=z i <;> by_cases hp : P x <;> simp_all [eq_comm]
    simp only [he]
    simp
  simp_rw [expand]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x,(if P x then (1:ℝ) else 0)*(Fintype.card V:ℝ)^(Fintype.card I-1) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hp : P x
      · simp only [hp,ite_true,one_mul]
        convert one_position_indicator_total i x using 1 <;> congr!
      · simp only [hp,ite_false,zero_mul,Finset.sum_const_zero]
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem tuple_unary_deletion_count (P : V → Prop) (i : I) (d : ℝ)
    (hP : (∑ x,if P x then (1:ℝ) else 0)≤d) :
    (∑ z : I → V,if P (z i) then (1:ℝ) else 0)≤
      d*(Fintype.card V:ℝ)^(Fintype.card I-1) := by
  rw [tuple_unary_indicator_count P i]
  exact mul_le_mul_of_nonneg_right hP (by positivity)

theorem finite_predicate_loss_union {A J : Type*} [Fintype A] [Fintype J]
    (P Q : A → Prop) (bad : J → A → Prop)
    (hbad : ∀ a,P a → ¬Q a → ∃ j,bad j a) :
    (Fintype.card {a // P a}:ℝ)-Fintype.card {a // Q a}≤
      ∑ j,∑ a,if bad j a then (1:ℝ) else 0 := by
  have he (T : A → Prop) : (Fintype.card {a // T a}:ℝ)=∑ a,if T a then (1:ℝ) else 0 := by
    simp only [Fintype.card_subtype,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [he P,he Q,← Finset.sum_sub_distrib,Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  have hnon : 0≤∑ j,if bad j a then (1:ℝ) else 0 :=
    Finset.sum_nonneg (fun j _=>by split_ifs <;> norm_num)
  by_cases hp : P a
  · by_cases hq : Q a
    · simpa only [hp,hq,ite_true,sub_self] using hnon
    · have hh := finite_exists_indicator_le_sum (fun j=>bad j a)
      have hex := hbad a hp hq
      simpa only [hp,hq,hex,ite_true,ite_false,sub_zero] using hh
  · by_cases hq : Q a
    · simp only [hp,hq,ite_true,ite_false,zero_sub];linarith
    · simpa only [hp,hq,ite_false,sub_self] using hnon

theorem finite_constraint_loss {A J : Type*} [Fintype A] [Fintype J]
    (base : A → Prop) (P Q : J → A → Prop) (M : ℝ)
    (hM : ∀ j,(∑ a,if P j a ∧ ¬Q j a then (1:ℝ) else 0)≤M) :
    (Fintype.card {a // base a ∧ ∀ j,P j a}:ℝ)-
      Fintype.card {a // base a ∧ ∀ j,Q j a}≤(Fintype.card J:ℝ)*M := by
  have hh := finite_predicate_loss_union (fun a=>base a ∧ ∀ j,P j a)
    (fun a=>base a ∧ ∀ j,Q j a) (fun j a=>P j a ∧ ¬Q j a) (by
      intro a hp hq
      have hnot : ¬∀ j,Q j a := fun h=>hq ⟨hp.1,h⟩
      push_neg at hnot
      obtain ⟨j,hj⟩ := hnot
      exact ⟨j,hp.2 j,hj⟩)
  have hbound : (∑ j,∑ a,if P j a ∧ ¬Q j a then (1:ℝ) else 0)≤(Fintype.card J:ℝ)*M := by
    calc
      _ ≤ ∑ _j : J,M := Finset.sum_le_sum (fun j _=>hM j)
      _ = _ := by simp
  convert (hh.trans (by convert hbound using 1 <;> congr!)) using 1 <;> congr!

end Oberwolfach
