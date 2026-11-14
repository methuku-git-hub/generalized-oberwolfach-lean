module

public import Oberwolfach.FiniteTransitionErrors

@[expose] public section

/-! Three ordinary steps mix even though the common-neighbourhood hypothesis
only applies to distinct endpoint labels. The omitted diagonal contributes
exactly one entry of the first transition matrix. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem transition_two_step_support_lower {X : Type*} [Fintype X]
    (R S : X → X → ℝ) (A : X → X → Prop) [DecidableRel A]
    (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hR : ∀ x y,0≤R x y) (hS : ∀ x y,0≤S x y)
    (hRa : ∀ x y,A x y → a≤R x y) (hSb : ∀ x y,A x y → b≤S x y)
    (x y : X) :
    ((Finset.univ.filter (fun z => A x z ∧ A z y)).card : ℝ)*(a*b) ≤
      transitionCompose R S x y := by
  classical
  have he : ((Finset.univ.filter (fun z => A x z ∧ A z y)).card : ℝ)*(a*b)=
      ∑ z,if A x z ∧ A z y then a*b else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [he]
  apply Finset.sum_le_sum
  intro z _
  split_ifs with hz
  · exact mul_le_mul (hRa x z hz.1) (hSb z y hz.2) hb (hR x z)
  · exact mul_nonneg (hR x z) (hS z y)

theorem transition_three_step_offdiagonal {X : Type*} [Fintype X]
    (R S T : X → X → ℝ) (hR : IsTransition R)
    (hS : ∀ x y,0≤S x y) (hT : ∀ x y,0≤T x y)
    (τ : ℝ) (hlower : ∀ z y,z≠y → τ≤transitionCompose S T z y) (x y : X) :
    τ*(1-R x y) ≤ transitionCompose R (transitionCompose S T) x y := by
  classical
  have hnonneg (z : X) : 0≤transitionCompose S T z y :=
    Finset.sum_nonneg fun u _ => mul_nonneg (hS z u) (hT u y)
  have he : (∑ z,if z=y then (0:ℝ) else R x z)=1-R x y := by
    have hi (z : X) : (if z=y then (0:ℝ) else R x z)=R x z-(if z=y then R x z else 0) := by
      split_ifs <;> ring
    simp only [hi,Finset.sum_sub_distrib,hR.2,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  calc
    τ*(1-R x y) = ∑ z,if z=y then 0 else R x z*τ := by
      rw [← he,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs with hz
      · exact mul_nonneg (hR.1 x z) (hnonneg z)
      · exact mul_le_mul_of_nonneg_left (hlower z y hz) (hR.1 x z)

theorem ordinary_three_step_minorization {X : Type*} [Fintype X]
    (R S T : X → X → ℝ) (A : X → X → Prop) [DecidableRel A]
    (μ : X → ℝ) (α p p₀ n : ℝ)
    (hα : 0<α) (hp₀ : 0<p₀) (hp : p₀≤p) (hn : 0<n) (hsize : 10/p₀≤n)
    (hR : IsTransition R) (hS : ∀ x y,0≤S x y) (hT : ∀ x y,0≤T x y)
    (hSup : ∀ x y,A x y → 1/(6*p*n)≤S x y)
    (hTup : ∀ x y,A x y → 1/(6*p*n)≤T x y)
    (hRu : ∀ x y,R x y≤5/(p*n))
    (hcommon : ∀ x y,x≠y → α*p^2*n ≤
      ((Finset.univ.filter (fun z => A x z ∧ A z y)).card : ℝ))
    (hμ : ∀ y,μ y≤2/n) (x y : X) :
    (α/200)*μ y ≤ transitionCompose R (transitionCompose S T) x y := by
  have hpp : 0<p := hp₀.trans_le hp
  have ht (z y : X) (hzy : z≠y) : α/(36*n)≤transitionCompose S T z y := by
    have hh := transition_two_step_support_lower S T A (1/(6*p*n)) (1/(6*p*n))
      (by positivity) (by positivity) hS hT hSup hTup z y
    have hm := mul_le_mul_of_nonneg_right (hcommon z y hzy)
      (show 0≤(1/(6*p*n))*(1/(6*p*n)) by positivity)
    have he : (α*p^2*n)*((1/(6*p*n))*(1/(6*p*n)))=α/(36*n) := by
      field_simp
      <;> ring
    rw [he] at hm
    exact hm.trans hh
  have hsize' : 10≤p*n := by
    have hh : 10≤n*p₀ := (div_le_iff₀ hp₀).mp hsize
    nlinarith [mul_le_mul_of_nonneg_right hp hn.le]
  have hhalf : R x y≤1/2 := by
    apply (hRu x y).trans
    apply (div_le_iff₀ (mul_pos hpp hn)).mpr
    linarith
  have hm := transition_three_step_offdiagonal R S T hR hS hT (α/(36*n)) ht x y
  have hbase : α/(72*n)≤(α/(36*n))*(1-R x y) := by
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0≤α/(36*n) by positivity)
    have hid : α/(36*n)/2=α/(72*n) := by ring
    linarith
  have hu := mul_le_mul_of_nonneg_left (hμ y) (show 0≤α/200 by positivity)
  have hnum : (α/200)*(2/n)≤α/(72*n) := by
    field_simp
    <;> nlinarith
  exact (hu.trans hnum).trans (hbase.trans hm)

end Oberwolfach
