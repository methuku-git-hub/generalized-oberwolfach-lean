module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Minimum squared Euclidean length in the convex hull of a finite family.
The ambient finite function space carries its usual topology; the energy
is written explicitly as the sum of the squared coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I Ω : Type*} [Fintype I]

def quadraticEnergy (z : I → ℝ) : ℝ := ∑ i,(z i)^2

theorem quadraticEnergy_nonneg (z : I → ℝ) : 0≤quadraticEnergy z :=
  Finset.sum_nonneg (fun i _=>sq_nonneg (z i))

theorem quadraticEnergy_mix (u v : I → ℝ) {θ : ℝ} (hθ0 : 0≤θ) (hθ1 : θ≤1) :
    quadraticEnergy (θ•u+(1-θ)•v)≤
      θ*quadraticEnergy u+(1-θ)*quadraticEnergy v := by
  simp only [quadraticEnergy,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change (θ*u i+(1-θ)*v i)^2≤θ*(u i)^2+(1-θ)*(v i)^2
  have h := mul_nonneg (mul_nonneg hθ0 (sub_nonneg.mpr hθ1)) (sq_nonneg (u i-v i))
  nlinarith

theorem finiteHull_energy_minimum (d : Ω → I → ℝ) (A : Finset Ω) (hA : A.Nonempty) :
    ∃ z∈convexHull ℝ (d '' (A : Set Ω)),
      ∀ y∈convexHull ℝ (d '' (A : Set Ω)),quadraticEnergy z≤quadraticEnergy y := by
  have hc := ((A.finite_toSet).image d).isCompact_convexHull ℝ
  have hn : (convexHull ℝ (d '' (A : Set Ω))).Nonempty := by
    obtain ⟨a,ha⟩ := hA
    exact ⟨d a,subset_convexHull ℝ _ (Set.mem_image_of_mem d ha)⟩
  exact hc.exists_isMinOn hn
    (show ContinuousOn quadraticEnergy _ by unfold quadraticEnergy;fun_prop)

def finiteHullEnergy (d : Ω → I → ℝ) (A : Finset Ω) : ℝ :=
  if hA : A.Nonempty then quadraticEnergy (Classical.choose (finiteHull_energy_minimum d A hA))
  else 0

theorem finiteHullEnergy_attained (d : Ω → I → ℝ) (A : Finset Ω) (hA : A.Nonempty) :
    ∃ z∈convexHull ℝ (d '' (A : Set Ω)),quadraticEnergy z=finiteHullEnergy d A ∧
      ∀ y∈convexHull ℝ (d '' (A : Set Ω)),finiteHullEnergy d A≤quadraticEnergy y := by
  rw [finiteHullEnergy,dif_pos hA]
  exact ⟨_,(Classical.choose_spec (finiteHull_energy_minimum d A hA)).1,rfl,
    (Classical.choose_spec (finiteHull_energy_minimum d A hA)).2⟩

theorem finiteHullEnergy_nonneg (d : Ω → I → ℝ) (A : Finset Ω) :
    0≤finiteHullEnergy d A := by
  unfold finiteHullEnergy
  split_ifs
  · exact quadraticEnergy_nonneg _
  · exact le_refl _

theorem finiteHullEnergy_le (d : Ω → I → ℝ) (A : Finset Ω) (hA : A.Nonempty)
    {z : I → ℝ} (hz : z∈convexHull ℝ (d '' (A : Set Ω))) :
    finiteHullEnergy d A≤quadraticEnergy z := by
  obtain ⟨_,_,_,hmin⟩ := finiteHullEnergy_attained d A hA
  exact hmin z hz

theorem finiteHullEnergy_antitone (d : Ω → I → ℝ) {A B : Finset Ω}
    (hA : A.Nonempty) (hAB : A⊆B) : finiteHullEnergy d B≤finiteHullEnergy d A := by
  obtain ⟨z,hz,he,_⟩ := finiteHullEnergy_attained d A hA
  rw [← he]
  exact finiteHullEnergy_le d B (hA.mono hAB)
    ((convexHull_mono (Set.image_mono hAB)) hz)

theorem finiteHull_coordinate_bounds (d : Ω → I → ℝ) (A : Finset Ω)
    (lo hi : I → ℝ) (hd : ∀ a∈A,∀ i,lo i≤d a i ∧ d a i≤hi i)
    {z : I → ℝ} (hz : z∈convexHull ℝ (d '' (A : Set Ω))) :
    ∀ i,lo i≤z i ∧ z i≤hi i := by
  have hsub : d '' (A : Set Ω)⊆Set.Icc lo hi := by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨fun i=>(hd a ha i).1,fun i=>(hd a ha i).2⟩
  have hb := (convexHull_min hsub (convex_Icc lo hi)) hz
  exact fun i=>⟨hb.1 i,hb.2 i⟩

theorem finiteHull_lift_linear {J : Type*} (P : (I → ℝ) →ₗ[ℝ] (J → ℝ))
    (d : Ω → I → ℝ) (A : Finset Ω) {u : J → ℝ}
    (hu : u∈convexHull ℝ ((fun a=>P (d a)) '' (A : Set Ω))) :
    ∃ z∈convexHull ℝ (d '' (A : Set Ω)),P z=u := by
  have he : (fun a=>P (d a)) '' (A : Set Ω)=P '' (d '' (A : Set Ω)) :=
    (Set.image_image P d (A : Set Ω)).symm
  rw [he,← P.image_convexHull] at hu
  exact hu

end Oberwolfach
