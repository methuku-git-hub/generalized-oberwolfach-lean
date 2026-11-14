module

public import Oberwolfach.ExceptionalSumBounds

@[expose] public section

/-! Adjacency indicators and the actual bipartite intersection sums used
in the alternating correction. Density profiles are supplied functions. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B]

def bipAdj (H : A → B → Prop) (x : A) (u : B) : ℝ := if H x u then 1 else 0

def bipColumnDegree (H : A → B → Prop) (u : B) : ℝ := ∑ x,bipAdj H x u

def bipPairIntersection (H : A → B → Prop) (u v : B) : ℝ :=
  ∑ x,bipAdj H x u*bipAdj H x v

def bipTripleIntersection (H : A → B → Prop) (u v t : B) : ℝ :=
  ∑ x,bipAdj H x u*bipAdj H x v*bipAdj H x t

def bipWeightedCodegree (H : A → B → Prop) (q : B → ℝ) (x y : A) : ℝ :=
  ∑ u,bipAdj H x u*bipAdj H y u*(q u)^2

theorem bipAdj_nonneg (H : A → B → Prop) (x : A) (u : B) : 0≤bipAdj H x u := by
  unfold bipAdj;split_ifs <;> norm_num

theorem bipAdj_le_one (H : A → B → Prop) (x : A) (u : B) : bipAdj H x u≤1 := by
  unfold bipAdj;split_ifs <;> norm_num

theorem bipAdj_sq (H : A → B → Prop) (x : A) (u : B) : (bipAdj H x u)^2=bipAdj H x u := by
  unfold bipAdj;split_ifs <;> norm_num

theorem bipColumnDegree_bounds (H : A → B → Prop) (u : B) :
    0≤bipColumnDegree H u ∧ bipColumnDegree H u≤Fintype.card A := by
  unfold bipColumnDegree
  constructor
  · exact Finset.sum_nonneg (fun x _=>bipAdj_nonneg H x u)
  · simpa using Finset.sum_le_sum (s:=Finset.univ) (fun x _=>bipAdj_le_one H x u)

theorem bipPairIntersection_bounds (H : A → B → Prop) (u v : B) :
    0≤bipPairIntersection H u v ∧ bipPairIntersection H u v≤Fintype.card A := by
  unfold bipPairIntersection
  constructor
  · exact Finset.sum_nonneg (fun x _=>mul_nonneg (bipAdj_nonneg H x u) (bipAdj_nonneg H x v))
  · calc
      _ ≤ ∑ _x : A,(1:ℝ) := by
        apply Finset.sum_le_sum;intro x _
        simpa using mul_le_mul (bipAdj_le_one H x u) (bipAdj_le_one H x v) (bipAdj_nonneg H x v) (by norm_num)
      _ = _ := by simp

theorem bipTripleIntersection_bounds (H : A → B → Prop) (u v t : B) :
    0≤bipTripleIntersection H u v t ∧ bipTripleIntersection H u v t≤Fintype.card A := by
  unfold bipTripleIntersection
  constructor
  · exact Finset.sum_nonneg (fun x _=>mul_nonneg
      (mul_nonneg (bipAdj_nonneg H x u) (bipAdj_nonneg H x v)) (bipAdj_nonneg H x t))
  · calc
      _ ≤ ∑ _x : A,(1:ℝ) := by
        apply Finset.sum_le_sum;intro x _
        unfold bipAdj;split_ifs <;> norm_num
      _ = _ := by simp

theorem bipWeightedCodegree_bounds (H : A → B → Prop) (q : B → ℝ)
    (L : ℝ) (hL : 0≤L) (hq : ∀ u,0≤q u ∧ q u≤L) (x y : A) :
    0≤bipWeightedCodegree H q x y ∧ bipWeightedCodegree H q x y≤L^2*Fintype.card B := by
  unfold bipWeightedCodegree
  constructor
  · exact Finset.sum_nonneg (fun u _=>mul_nonneg
      (mul_nonneg (bipAdj_nonneg H x u) (bipAdj_nonneg H y u)) (sq_nonneg _))
  · calc
      _ ≤ ∑ _u : B,L^2 := by
        apply Finset.sum_le_sum;intro u _
        have hh : (q u)^2≤L^2 := pow_le_pow_left₀ (hq u).1 (hq u).2 2
        unfold bipAdj
        split_ifs <;> simp_all
      _ = _ := by simp;ring

theorem bipWeightedCodegree_absolute_error (H : A → B → Prop) (q : B → ℝ)
    (L : ℝ) (hL : 0≤L) (hq : ∀ u,0≤q u ∧ q u≤L) (x y : A) :
    |bipWeightedCodegree H q x y-(Fintype.card B:ℝ)|≤(L^2+1)*Fintype.card B := by
  have hb := bipWeightedCodegree_bounds H q L hL hq x y
  rw [abs_le]
  constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card B)]

theorem bipWeightedCodegree_error_sum [DecidableEq A]
    (H : A → B → Prop) (q : B → ℝ) (L δ D : ℝ)
    (hL : 0≤L) (hδ : 0≤δ) (hq : ∀ u,0≤q u ∧ q u≤L)
    (E : A → Finset A) (hE : ∀ x,(E x).card≤D)
    (herr : ∀ x y,y∉E x → |bipWeightedCodegree H q x y-(Fintype.card B:ℝ)|≤δ*Fintype.card B)
    (x : A) :
    (∑ y,|bipWeightedCodegree H q x y-(Fintype.card B:ℝ)|)≤
      (Fintype.card A:ℝ)*δ*Fintype.card B+D*(L^2+1)*Fintype.card B := by
  have hh := exceptional_sum_abs_le (fun y=>bipWeightedCodegree H q x y-(Fintype.card B:ℝ))
    (E x) (δ*Fintype.card B) ((L^2+1)*Fintype.card B) (by positivity) (by positivity)
    (herr x) (bipWeightedCodegree_absolute_error H q L hL hq x)
  calc
    _ ≤ (Fintype.card A:ℝ)*(δ*Fintype.card B)+((E x).card:ℝ)*((L^2+1)*Fintype.card B) := hh
    _ ≤ (Fintype.card A:ℝ)*(δ*Fintype.card B)+D*((L^2+1)*Fintype.card B) := by gcongr;exact hE x
    _ = _ := by ring

end Oberwolfach
