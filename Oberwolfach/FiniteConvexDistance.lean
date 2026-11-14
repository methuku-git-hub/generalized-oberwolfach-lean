module

public import Oberwolfach.FiniteConvexEnergy
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! Convex distance to a set of configurations. Its square is the least
sum of squared coordinate-disagreement probabilities among convex
combinations of the configurations in the target set. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I J Ω Γ : Type*} [Fintype I]

theorem finiteHullEnergy_eq_of_hulls
    (d : Ω → I → ℝ) (e : Γ → I → ℝ) (A : Finset Ω) (B : Finset Γ)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (heq : convexHull ℝ (d '' (A : Set Ω))=convexHull ℝ (e '' (B : Set Γ))) :
    finiteHullEnergy d A=finiteHullEnergy e B := by
  obtain ⟨x,hx,hex,_⟩ := finiteHullEnergy_attained d A hA
  obtain ⟨y,hy,hey,_⟩ := finiteHullEnergy_attained e B hB
  apply le_antisymm
  · rw [← hey]
    exact finiteHullEnergy_le d A hA (heq.symm ▸ hy)
  · rw [← hex]
    exact finiteHullEnergy_le e B hB (heq ▸ hx)

theorem finiteHullEnergy_image [DecidableEq Γ]
    (d : Γ → I → ℝ) (f : Ω → Γ) (A : Finset Ω) :
    finiteHullEnergy d (A.image f)=finiteHullEnergy (fun a=>d (f a)) A := by
  by_cases hA : A.Nonempty
  · apply finiteHullEnergy_eq_of_hulls d (fun a=>d (f a)) (A.image f) A
      (hA.image f) hA
    rw [Finset.coe_image,Set.image_image]
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [he,finiteHullEnergy]

def coordinateReindexLinear (e : I ≃ J) : (J → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun z i := z (e i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quadraticEnergy_reindex [Fintype J] (e : I ≃ J) (z : J → ℝ) :
    quadraticEnergy (coordinateReindexLinear e z)=quadraticEnergy z :=
  e.sum_comp (fun j=>(z j)^2)

theorem finiteHullEnergy_reindex [Fintype J] (e : I ≃ J)
    (d : Ω → J → ℝ) (A : Finset Ω) :
    finiteHullEnergy (fun a=>coordinateReindexLinear e (d a)) A=finiteHullEnergy d A := by
  by_cases hA : A.Nonempty
  · obtain ⟨x,hx,hex,_⟩ := finiteHullEnergy_attained d A hA
    obtain ⟨y,hy,hey,_⟩ :=
      finiteHullEnergy_attained (fun a=>coordinateReindexLinear e (d a)) A hA
    have him : coordinateReindexLinear e x∈
        convexHull ℝ ((fun a=>coordinateReindexLinear e (d a)) '' (A : Set Ω)) := by
      rw [← Set.image_image,← (coordinateReindexLinear e).image_convexHull]
      exact Set.mem_image_of_mem _ hx
    obtain ⟨z,hz,hzy⟩ := finiteHull_lift_linear (coordinateReindexLinear e) d A hy
    apply le_antisymm
    · calc
        _ ≤ quadraticEnergy (coordinateReindexLinear e x) :=
          finiteHullEnergy_le _ A hA him
        _ = quadraticEnergy x := quadraticEnergy_reindex e x
        _ = _ := hex
    · calc
        _ ≤ quadraticEnergy z := finiteHullEnergy_le d A hA hz
        _ = quadraticEnergy y := by rw [← hzy,quadraticEnergy_reindex]
        _ = _ := hey
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [he,finiteHullEnergy]

def disagreementVector (x y : I → Ω) (i : I) : ℝ :=
  if x i=y i then 0 else 1

def convexDistanceSq (A : Finset (I → Ω)) (x : I → Ω) : ℝ :=
  finiteHullEnergy (disagreementVector x) A

theorem convexDistanceSq_nonneg (A : Finset (I → Ω)) (x : I → Ω) :
    0≤convexDistanceSq A x :=
  finiteHullEnergy_nonneg _ _

theorem convexDistanceSq_mem (A : Finset (I → Ω)) {x : I → Ω} (hx : x∈A) :
    convexDistanceSq A x=0 := by
  apply le_antisymm
  · have h := finiteHullEnergy_le (disagreementVector x) A ⟨x,hx⟩
      (subset_convexHull ℝ _ (Set.mem_image_of_mem (disagreementVector x) hx))
    simpa only [convexDistanceSq,quadraticEnergy,disagreementVector,ite_true,zero_pow (by decide : 2≠0),
      Finset.sum_const_zero] using h
  · exact convexDistanceSq_nonneg A x

theorem convexDistanceSq_le_card (A : Finset (I → Ω)) (x : I → Ω) :
    convexDistanceSq A x≤Fintype.card I := by
  by_cases hA : A.Nonempty
  · obtain ⟨y,hy⟩ := hA
    have h := finiteHullEnergy_le (disagreementVector x) A ⟨y,hy⟩
      (subset_convexHull ℝ _ (Set.mem_image_of_mem (disagreementVector x) hy))
    apply h.trans
    calc
      _ ≤ ∑ _ : I,(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [disagreementVector]
        split_ifs <;> norm_num
      _ = _ := by simp
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [he,convexDistanceSq,finiteHullEnergy]

end Oberwolfach
