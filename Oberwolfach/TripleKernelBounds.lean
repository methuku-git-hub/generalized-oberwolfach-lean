module

public import Oberwolfach.SparseOppositeSquare
public import Oberwolfach.BipartitePairError

@[expose] public section

/-! The triple-intersection kernel estimates, including both exceptional
row pairs and repeated column indices. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem bipTripleKernel_bounds (H : A → B → Prop) (q : B → ℝ)
    (L : ℝ) (hL : 0≤L) (hq : ∀ u,0≤q u ∧ q u≤L) (x s : A) (u t : B) :
    0≤bipTripleKernel H q x u s t ∧
      bipTripleKernel H q x u s t≤L^3*(Fintype.card A:ℝ)*Fintype.card B := by
  unfold bipTripleKernel
  have hpoint (v : B) : 0≤bipAdj H x v*bipAdj H s v*(q v)^3*bipTripleIntersection H u v t ∧
      bipAdj H x v*bipAdj H s v*(q v)^3*bipTripleIntersection H u v t≤L^3*Fintype.card A := by
    have hqv := (hq v).1
    have hI := bipTripleIntersection_bounds H u v t
    constructor
    · exact mul_nonneg (mul_nonneg (mul_nonneg (bipAdj_nonneg H x v) (bipAdj_nonneg H s v))
        (pow_nonneg hqv 3)) hI.1
    · unfold bipAdj
      split_ifs <;> simp only [one_mul,zero_mul]
      all_goals first
      | positivity
      | exact mul_le_mul (pow_le_pow_left₀ hqv (hq v).2 3) hI.2 hI.1 (by positivity)
  constructor
  · exact Finset.sum_nonneg (fun v _=>(hpoint v).1)
  · calc
      _ ≤ ∑ _v : B,L^3*Fintype.card A := Finset.sum_le_sum (fun v _=>(hpoint v).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

theorem bipTripleKernel_codegree_error (H : A → B → Prop) (p q : B → ℝ)
    (L δ : ℝ) (hL : 0≤L) (hδ : 0≤δ)
    (hp : ∀ u,0≤p u ∧ p u≤1) (hq : ∀ u,0≤q u ∧ q u≤L) (hpq : ∀ u,q u*p u=1)
    (herr : ∀ u v t,u≠v → u≠t → v≠t →
      |bipTripleIntersection H u v t-(Fintype.card A:ℝ)*p u*p v*p t|≤δ*Fintype.card A)
    (x s : A) (u t : B) (hut : u≠t) :
    |bipTripleKernel H q x u s t-(Fintype.card A:ℝ)*p u*p t*bipWeightedCodegree H q x s|≤
      L^3*((Fintype.card B:ℝ)*δ*Fintype.card A+4*Fintype.card A) := by
  have he : bipTripleKernel H q x u s t-(Fintype.card A:ℝ)*p u*p t*bipWeightedCodegree H q x s=
      ∑ v,(bipAdj H x v*bipAdj H s v*(q v)^3)*
        (bipTripleIntersection H u v t-(Fintype.card A:ℝ)*p u*p v*p t) := by
    unfold bipTripleKernel bipWeightedCodegree
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl;intro v _
    have hqp : (q v)^3*p v=(q v)^2 := by
      calc
        _ = (q v)^2*(q v*p v) := by ring
        _ = _ := by rw [hpq v,mul_one]
    calc
      _ = bipAdj H x v*bipAdj H s v*(Fintype.card A:ℝ)*p u*p t*(q v)^2 := by ring
      _ = _ := by rw [← hqp];ring
  rw [he]
  have hfactor (v : B) : |bipAdj H x v*bipAdj H s v*(q v)^3|≤L^3 := by
    have hqv := (hq v).1
    unfold bipAdj
    split_ifs <;> simp only [one_mul,zero_mul,abs_zero]
    all_goals first
    | positivity
    | rw [abs_of_nonneg (pow_nonneg hqv 3)]
      exact pow_le_pow_left₀ hqv (hq v).2 3
  exact (weighted_sum_abs_le _ _ (L^3) (by positivity) hfactor).trans
    (mul_le_mul_of_nonneg_left (bipTripleIntersection_error_sum H p hp δ hδ herr u t hut) (by positivity))

theorem bipTripleKernel_absolute_error (H : A → B → Prop) (p q : B → ℝ)
    (L : ℝ) (hL : 0≤L) (hp : ∀ u,0≤p u ∧ p u≤1) (hq : ∀ u,0≤q u ∧ q u≤L)
    (x s : A) (u t : B) :
    |bipTripleKernel H q x u s t-(Fintype.card A:ℝ)*(Fintype.card B:ℝ)*p u*p t|≤
      (L^3+1)*(Fintype.card A:ℝ)*Fintype.card B := by
  have hb := bipTripleKernel_bounds H q L hL hq x s u t
  have hpu := (hp u).1
  have hpt := (hp t).1
  have hc : 0≤(Fintype.card A:ℝ)*(Fintype.card B:ℝ)*p u*p t := by positivity
  have hu : (Fintype.card A:ℝ)*(Fintype.card B:ℝ)*p u*p t≤(Fintype.card A:ℝ)*Fintype.card B := by
    calc
      _ ≤ (Fintype.card A:ℝ)*(Fintype.card B:ℝ)*1*1 := by gcongr <;> exact (hp _).2
      _ = _ := by ring
  rw [abs_le]
  constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card A),Nat.cast_nonneg (α:=ℝ) (Fintype.card B)]

theorem bipTripleKernel_regular_error (H : A → B → Prop) (p q : B → ℝ)
    (L δ : ℝ) (hL : 0≤L) (hδ : 0≤δ)
    (hp : ∀ u,0≤p u ∧ p u≤1) (hq : ∀ u,0≤q u ∧ q u≤L) (hpq : ∀ u,q u*p u=1)
    (herr : ∀ u v t,u≠v → u≠t → v≠t →
      |bipTripleIntersection H u v t-(Fintype.card A:ℝ)*p u*p v*p t|≤δ*Fintype.card A)
    (x s : A) (u t : B) (hut : u≠t)
    (hxs : |bipWeightedCodegree H q x s-(Fintype.card B:ℝ)|≤δ*Fintype.card B) :
    |bipTripleKernel H q x u s t-(Fintype.card A:ℝ)*(Fintype.card B:ℝ)*p u*p t|≤
      L^3*((Fintype.card B:ℝ)*δ*Fintype.card A+4*Fintype.card A)+
        (Fintype.card A:ℝ)*δ*Fintype.card B := by
  have hpu := (hp u).1
  have hpt := (hp t).1
  have hcoeff : (Fintype.card A:ℝ)*p u*p t≤Fintype.card A := by
    calc
      _ ≤ (Fintype.card A:ℝ)*1*1 := by gcongr <;> exact (hp _).2
      _ = _ := by ring
  have hrest : |(Fintype.card A:ℝ)*p u*p t*bipWeightedCodegree H q x s-
      (Fintype.card A:ℝ)*(Fintype.card B:ℝ)*p u*p t|≤(Fintype.card A:ℝ)*δ*Fintype.card B := by
    calc
      _ = |(Fintype.card A:ℝ)*p u*p t*(bipWeightedCodegree H q x s-(Fintype.card B:ℝ))| := by congr 1;ring
      _ = ((Fintype.card A:ℝ)*p u*p t)*|bipWeightedCodegree H q x s-(Fintype.card B:ℝ)| := by
        rw [abs_mul,abs_of_nonneg (by positivity)]
      _ ≤ (Fintype.card A:ℝ)*(δ*Fintype.card B) :=
        mul_le_mul hcoeff hxs (abs_nonneg _) (Nat.cast_nonneg _)
      _ = _ := by ring
  exact (abs_sub_le _ ((Fintype.card A:ℝ)*p u*p t*bipWeightedCodegree H q x s) _).trans
    (add_le_add (bipTripleKernel_codegree_error H p q L δ hL hδ hp hq hpq herr x s u t hut) hrest)

end Oberwolfach
