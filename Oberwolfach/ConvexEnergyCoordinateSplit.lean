module

public import Oberwolfach.FiniteConvexEnergy
public import Mathlib.Algebra.BigOperators.Option

@[expose] public section

/-! Removing one coordinate from a finite convex-hull minimisation.
The additional coordinate of a convex combination contributes at most
the square of the weight assigned to the unrestricted fibre. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I Ω : Type*} [Fintype I]

def optionTailLinear : (Option I → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun z i := z (some i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quadraticEnergy_option (z : Option I → ℝ) :
    quadraticEnergy z=(z none)^2+quadraticEnergy (optionTailLinear z) := by
  simp only [quadraticEnergy,Fintype.sum_option,optionTailLinear,LinearMap.coe_mk,
    AddHom.coe_mk]

theorem finiteHullEnergy_coordinate_projection
    (d : Ω → Option I → ℝ) (A : Finset Ω) (hA : A.Nonempty)
    (hd : ∀ a∈A,0≤d a none ∧ d a none≤1) :
    finiteHullEnergy d A≤finiteHullEnergy (fun a=>optionTailLinear (d a)) A+1 := by
  obtain ⟨u,hu,he,_⟩ := finiteHullEnergy_attained (fun a=>optionTailLinear (d a)) A hA
  obtain ⟨z,hz,hzu⟩ := finiteHull_lift_linear optionTailLinear d A hu
  have hbound : 0≤z none ∧ z none≤1 := by
    have hsub : d '' (A : Set Ω)⊆{z | 0≤z none ∧ z none≤1} := by
      rintro _ ⟨a,ha,rfl⟩
      exact hd a ha
    have hconv : Convex ℝ {z : Option I → ℝ | 0≤z none ∧ z none≤1} := by
      intro x hx y hy a b ha hb hab
      change 0≤a*x none+b*y none ∧ a*x none+b*y none≤1
      constructor
      · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
      · nlinarith [mul_le_mul_of_nonneg_left hx.2 ha,mul_le_mul_of_nonneg_left hy.2 hb]
    exact (convexHull_min hsub hconv) hz
  calc
    _ ≤ quadraticEnergy z := finiteHullEnergy_le d A hA hz
    _ = (z none)^2+quadraticEnergy u := by rw [quadraticEnergy_option,hzu]
    _ ≤ _ := by rw [he];nlinarith

theorem finiteHullEnergy_coordinate_mix
    (d : Ω → Option I → ℝ) (A B : Finset Ω) (hA : A.Nonempty) (hBA : B⊆A)
    (hB : B.Nonempty) (hd : ∀ a∈A,0≤d a none ∧ d a none≤1)
    (hzero : ∀ a∈B,d a none=0)
    {θ : ℝ} (hθ0 : 0≤θ) (hθ1 : θ≤1) :
    finiteHullEnergy d A≤
      θ*finiteHullEnergy (fun a=>optionTailLinear (d a)) B+
      (1-θ)*finiteHullEnergy (fun a=>optionTailLinear (d a)) A+(1-θ)^2 := by
  obtain ⟨u,hu,heu,_⟩ := finiteHullEnergy_attained (fun a=>optionTailLinear (d a)) B hB
  obtain ⟨v,hv,hev,_⟩ := finiteHullEnergy_attained (fun a=>optionTailLinear (d a)) A hA
  obtain ⟨z,hz,hzu⟩ := finiteHull_lift_linear optionTailLinear d B hu
  obtain ⟨w,hw,hwv⟩ := finiteHull_lift_linear optionTailLinear d A hv
  have hz0 : z none=0 := by
    have hsub : d '' (B : Set Ω)⊆{z | z none=0} := by
      rintro _ ⟨a,ha,rfl⟩
      exact hzero a ha
    have hconv : Convex ℝ {z : Option I → ℝ | z none=0} := by
      intro x hx y hy a b _ _ _
      change a*x none+b*y none=0
      rw [hx,hy];ring
    exact (convexHull_min hsub hconv) hz
  have hw01 : 0≤w none ∧ w none≤1 := by
    have hsub : d '' (A : Set Ω)⊆{z | 0≤z none ∧ z none≤1} := by
      rintro _ ⟨a,ha,rfl⟩
      exact hd a ha
    have hconv : Convex ℝ {z : Option I → ℝ | 0≤z none ∧ z none≤1} := by
      intro x hx y hy a b ha hb hab
      change 0≤a*x none+b*y none ∧ a*x none+b*y none≤1
      constructor
      · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
      · nlinarith [mul_le_mul_of_nonneg_left hx.2 ha,mul_le_mul_of_nonneg_left hy.2 hb]
    exact (convexHull_min hsub hconv) hw
  have hmix : θ•z+(1-θ)•w∈convexHull ℝ (d '' (A : Set Ω)) :=
    (convex_convexHull ℝ _)
      ((convexHull_mono (Set.image_mono hBA)) hz) hw hθ0 (sub_nonneg.mpr hθ1) (by ring)
  have hnone : ((θ•z+(1-θ)•w) none)^2≤(1-θ)^2 := by
    change (θ*z none+(1-θ)*w none)^2≤(1-θ)^2
    rw [hz0,mul_zero,zero_add]
    have hb : 0≤(1-θ)*w none := mul_nonneg (sub_nonneg.mpr hθ1) hw01.1
    have hupp : (1-θ)*w none≤1-θ := by nlinarith [hw01.2]
    nlinarith
  have htail : quadraticEnergy (optionTailLinear (θ•z+(1-θ)•w))≤
      θ*quadraticEnergy u+(1-θ)*quadraticEnergy v := by
    rw [map_add,map_smul,map_smul,hzu,hwv]
    exact quadraticEnergy_mix u v hθ0 hθ1
  have hmin := finiteHullEnergy_le d A hA hmix
  rw [quadraticEnergy_option] at hmin
  rw [heu,hev] at htail
  linarith

end Oberwolfach
