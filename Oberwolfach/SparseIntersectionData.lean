module

public import Oberwolfach.BipartitePairError

@[expose] public section

/-! The three explicit intersection hypotheses for sparse alternating
correction. The inverse profile is tied to the supplied density profile. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

structure SparseIntersectionData {A B : Type*} [Fintype A] [Fintype B]
    (H : A → B → Prop) (p q : B → ℝ) (L δ D : ℝ) : Prop where
  one_le_L : 1≤L
  delta_nonneg : 0≤δ
  D_nonneg : 0≤D
  density : ∀ u,0≤p u ∧ p u≤1
  inverse_bounds : ∀ u,0≤q u ∧ q u≤L
  inverse_identity : ∀ u,q u*p u=1
  degree_error : ∀ u,|bipColumnDegree H u-(Fintype.card A:ℝ)*p u|≤δ*Fintype.card A
  pair_error : ∀ u v,u≠v → |bipPairIntersection H v u-(Fintype.card A:ℝ)*p v*p u|≤δ*Fintype.card A
  triple_error : ∀ u v t,u≠v → u≠t → v≠t →
    |bipTripleIntersection H u v t-(Fintype.card A:ℝ)*p u*p v*p t|≤δ*Fintype.card A
  exceptions : ∀ x,∃ E : Finset A,(E.card:ℝ)≤D ∧
    ∀ y,y∉E → |bipWeightedCodegree H q x y-(Fintype.card B:ℝ)|≤δ*Fintype.card B

namespace SparseIntersectionData
variable {A B : Type*} [Fintype A] [Fintype B]
    {H : A → B → Prop} {p q : B → ℝ} {L δ D : ℝ}

theorem L_nonneg (h : SparseIntersectionData H p q L δ D) : 0≤L := le_trans zero_le_one h.one_le_L

noncomputable def exceptionalSets (h : SparseIntersectionData H p q L δ D) (x : A) : Finset A :=
  Classical.choose (h.exceptions x)

theorem exceptionalSets_card (h : SparseIntersectionData H p q L δ D) (x : A) :
    ((h.exceptionalSets x).card:ℝ)≤D := (Classical.choose_spec (h.exceptions x)).1

theorem exceptionalSets_error (h : SparseIntersectionData H p q L δ D) (x y : A)
    (hy : y∉h.exceptionalSets x) :
    |bipWeightedCodegree H q x y-(Fintype.card B:ℝ)|≤δ*Fintype.card B :=
  (Classical.choose_spec (h.exceptions x)).2 y hy

end SparseIntersectionData

theorem sparse_first_error_scalar (L δ d s : ℝ) (hL : 1≤L) (hδ : 0≤δ) (hd : 0≤d) (hs : 0≤s) :
    L*(2*δ+(L^2+1)*d)+L*(δ+(L^2+1)*d)+L^3*(δ+2*s)≤8*L^3*(δ+d+s) := by
  have hL0 : 0≤L := by linarith
  have hL2 : 1≤L^2 := one_le_pow₀ hL
  have hL3 : L≤L^3 := by nlinarith
  have h1 : 3*L+L^3≤4*L^3 := by linarith
  have h2 : 2*L*(L^2+1)≤4*L^3 := by nlinarith
  have h3 : 2*L^3≤4*L^3 := by nlinarith [pow_nonneg hL0 3]
  nlinarith [mul_le_mul_of_nonneg_right h1 hδ,mul_le_mul_of_nonneg_right h2 hd,
    mul_le_mul_of_nonneg_right h3 hs]

theorem sparse_second_error_scalar (L δ d s : ℝ) (hL : 1≤L) (hδ : 0≤δ) (hd : 0≤d) (hs : 0≤s) :
    L^3*((L^3+1)*δ+(L^3+1)*d+(5*L^3+1)*s)≤8*L^6*(δ+d+s) := by
  have hL0 : 0≤L := by linarith
  have hL3 : 1≤L^3 := one_le_pow₀ hL
  have h1 : L^3+1≤8*L^3 := by linarith
  have h2 : 5*L^3+1≤8*L^3 := by linarith
  have hh : (L^3+1)*δ+(L^3+1)*d+(5*L^3+1)*s≤8*L^3*(δ+d+s) := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hδ,mul_le_mul_of_nonneg_right h1 hd,
      mul_le_mul_of_nonneg_right h2 hs]
  calc
    _ ≤ L^3*(8*L^3*(δ+d+s)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end Oberwolfach
