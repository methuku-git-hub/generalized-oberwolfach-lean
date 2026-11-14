module

public import Oberwolfach.FiniteConvexDistance
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-! A certificate whose total coordinate weight is bounded gives a lower
bound on convex distance to every configuration with a smaller value. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I Ω : Type*} [Fintype I]

theorem convexDistanceSq_certificate
    (A : Finset (I → Ω)) (hA : A.Nonempty) (x : I → Ω)
    (w : I → ℝ) {c D t : ℝ} (hc : 0≤c) (ht : 0≤t)
    (hw : ∀ i,0≤w i ∧ w i≤c) (hD : ∑ i,w i≤D)
    (hsep : ∀ y∈A,t≤∑ i,w i*disagreementVector x y i) :
    t^2≤c*D*convexDistanceSq A x := by
  obtain ⟨z,hz,he,_⟩ := finiteHullEnergy_attained (disagreementVector x) A hA
  have hlower : t≤∑ i,w i*z i := by
    have hsub : disagreementVector x '' (A : Set (I → Ω))⊆
        {z | t≤∑ i,w i*z i} := by
      rintro _ ⟨y,hy,rfl⟩
      exact hsep y hy
    have hconv : Convex ℝ {z : I → ℝ | t≤∑ i,w i*z i} := by
      intro u hu v hv a b ha hb hab
      change t≤∑ i,w i*(a*u i+b*v i)
      have heq : (∑ i,w i*(a*u i+b*v i))=a*(∑ i,w i*u i)+b*(∑ i,w i*v i) := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [heq]
      nlinarith [mul_le_mul_of_nonneg_left hu ha,mul_le_mul_of_nonneg_left hv hb]
    exact (convexHull_min hsub hconv) hz
  have hsq : (∑ i,(w i)^2)≤c*D := by
    calc
      _ ≤ ∑ i,c*w i := Finset.sum_le_sum (fun i _=>by
        nlinarith [(hw i).1,(hw i).2])
      _ = c*∑ i,w i := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hD hc
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w z
  have hz0 : 0≤∑ i,(z i)^2 := Finset.sum_nonneg (fun i _=>sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hsq hz0
  change (∑ i,(z i)^2)=convexDistanceSq A x at he
  rw [he] at hCS hm
  nlinarith

theorem convexDistanceSq_value_certificate
    (R : (I → Ω) → ℝ) (A : Finset (I → Ω)) (hA : A.Nonempty)
    (x : I → Ω) (w : I → ℝ) {c D m t : ℝ} (hc : 0≤c) (ht : 0≤t)
    (hw : ∀ i,0≤w i ∧ w i≤c) (hD : ∑ i,w i≤D)
    (hAvalue : ∀ y∈A,R y≤m) (hxvalue : m+t≤R x)
    (hcert : ∀ y,R x≤R y+∑ i,if x i≠y i then w i else 0) :
    t^2≤c*D*convexDistanceSq A x := by
  apply convexDistanceSq_certificate A hA x w hc ht hw hD
  intro y hy
  have heq : (∑ i,if x i≠y i then w i else 0)=
      ∑ i,w i*disagreementVector x y i := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i=y i <;> simp [disagreementVector,h]
  have hh := hcert y
  rw [heq] at hh
  linarith [hAvalue y hy]

end Oberwolfach
