module

public import Oberwolfach.SparseIntersectionData

@[expose] public section

/-! Deletion estimates keep the supplied density and inverse-density profiles
fixed. No root domain, exceptional set or coefficient is recomputed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B]

theorem unit_product_deletion {a a' b b' : ℝ}
    (ha0 : 0≤a') (ha : a'≤a) (ha1 : a≤1)
    (hb0 : 0≤b') (hb : b'≤b) (hb1 : b≤1) :
    0≤a*b-a'*b' ∧ a*b-a'*b'≤(a-a')+(b-b') := by
  constructor
  · have hh := mul_le_mul ha hb hb0 (ha0.trans ha)
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hb1 (sub_nonneg.mpr ha)
    have h2 := mul_le_mul_of_nonneg_right (ha.trans ha1) (sub_nonneg.mpr hb)
    nlinarith

theorem bipAdj_deletion (H H' : A → B → Prop) (hsub : ∀ x u,H' x u → H x u)
    (x : A) (u : B) :
    bipAdj H x u-bipAdj H' x u=bipAdj (fun x u=>H x u ∧ ¬H' x u) x u := by
  have hh := hsub x u
  unfold bipAdj
  split_ifs <;> simp_all

theorem bipAdj_subrelation (H H' : A → B → Prop) (hsub : ∀ x u,H' x u → H x u)
    (x : A) (u : B) : bipAdj H' x u≤bipAdj H x u := by
  have hh := bipAdj_deletion H H' hsub x u
  have hn := bipAdj_nonneg (fun x u=>H x u ∧ ¬H' x u) x u
  linarith

theorem bipColumnDegree_deletion (H H' : A → B → Prop) (hsub : ∀ x u,H' x u → H x u)
    (u : B) (d : ℝ) (hd : (∑ x,bipAdj (fun x u=>H x u ∧ ¬H' x u) x u)≤d) :
    |bipColumnDegree H' u-bipColumnDegree H u|≤d := by
  have he : bipColumnDegree H u-bipColumnDegree H' u=
      ∑ x,bipAdj (fun x u=>H x u ∧ ¬H' x u) x u := by
    simp only [bipColumnDegree,← Finset.sum_sub_distrib,bipAdj_deletion H H' hsub]
  have hn : 0≤bipColumnDegree H u-bipColumnDegree H' u := by
    rw [he];exact Finset.sum_nonneg (fun x _=>bipAdj_nonneg _ _ _)
  rw [abs_sub_comm,abs_of_nonneg hn,he]
  exact hd

theorem bipPairIntersection_deletion (H H' : A → B → Prop) (hsub : ∀ x u,H' x u → H x u)
    (u v : B) (d : ℝ) (hd : ∀ u,(∑ x,bipAdj (fun x u=>H x u ∧ ¬H' x u) x u)≤d) :
    |bipPairIntersection H' u v-bipPairIntersection H u v|≤2*d := by
  have hp (x : A) := unit_product_deletion
    (bipAdj_nonneg H' x u) (bipAdj_subrelation H H' hsub x u) (bipAdj_le_one H x u)
    (bipAdj_nonneg H' x v) (bipAdj_subrelation H H' hsub x v) (bipAdj_le_one H x v)
  have he : bipPairIntersection H u v-bipPairIntersection H' u v=
      ∑ x,(bipAdj H x u*bipAdj H x v-bipAdj H' x u*bipAdj H' x v) := by
    simp only [bipPairIntersection,Finset.sum_sub_distrib]
  have hn : 0≤bipPairIntersection H u v-bipPairIntersection H' u v := by
    rw [he];exact Finset.sum_nonneg (fun x _=>(hp x).1)
  rw [abs_sub_comm,abs_of_nonneg hn,he]
  calc
    _ ≤ ∑ x,((bipAdj H x u-bipAdj H' x u)+(bipAdj H x v-bipAdj H' x v)) :=
      Finset.sum_le_sum (fun x _=>(hp x).2)
    _ ≤ 2*d := by
      simp only [bipAdj_deletion H H' hsub,Finset.sum_add_distrib]
      linarith only [hd u,hd v]

theorem bipTripleIntersection_deletion (H H' : A → B → Prop) (hsub : ∀ x u,H' x u → H x u)
    (u v t : B) (d : ℝ) (hd : ∀ u,(∑ x,bipAdj (fun x u=>H x u ∧ ¬H' x u) x u)≤d) :
    |bipTripleIntersection H' u v t-bipTripleIntersection H u v t|≤3*d := by
  have hp (x : A) := unit_product_deletion
    (bipAdj_nonneg H' x u) (bipAdj_subrelation H H' hsub x u) (bipAdj_le_one H x u)
    (bipAdj_nonneg H' x v) (bipAdj_subrelation H H' hsub x v) (bipAdj_le_one H x v)
  have hp1 (x : A) : bipAdj H x u*bipAdj H x v≤1 := by
    have hh := mul_le_mul (bipAdj_le_one H x u) (bipAdj_le_one H x v) (bipAdj_nonneg H x v) (by norm_num)
    simpa using hh
  have ht (x : A) := unit_product_deletion
    (mul_nonneg (bipAdj_nonneg H' x u) (bipAdj_nonneg H' x v)) (sub_nonneg.mp (hp x).1) (hp1 x)
    (bipAdj_nonneg H' x t) (bipAdj_subrelation H H' hsub x t) (bipAdj_le_one H x t)
  have he : bipTripleIntersection H u v t-bipTripleIntersection H' u v t=
      ∑ x,(bipAdj H x u*bipAdj H x v*bipAdj H x t-bipAdj H' x u*bipAdj H' x v*bipAdj H' x t) := by
    simp only [bipTripleIntersection,Finset.sum_sub_distrib]
  have hn : 0≤bipTripleIntersection H u v t-bipTripleIntersection H' u v t := by
    rw [he];exact Finset.sum_nonneg (fun x _=>(ht x).1)
  rw [abs_sub_comm,abs_of_nonneg hn,he]
  calc
    _ ≤ ∑ x,((bipAdj H x u-bipAdj H' x u)+(bipAdj H x v-bipAdj H' x v)+(bipAdj H x t-bipAdj H' x t)) := by
      apply Finset.sum_le_sum
      intro x _
      linarith only [(hp x).2,(ht x).2]
    _ ≤ 3*d := by
      simp only [bipAdj_deletion H H' hsub,Finset.sum_add_distrib]
      linarith only [hd u,hd v,hd t]

theorem bipWeightedCodegree_deletion (H H' : A → B → Prop) (hsub : ∀ x u,H' x u → H x u)
    (q : B → ℝ) (L d : ℝ) (hq : ∀ u,0≤q u ∧ q u≤L)
    (hd : ∀ x,(∑ u,bipAdj (fun x u=>H x u ∧ ¬H' x u) x u)≤d) (x y : A) :
    |bipWeightedCodegree H' q x y-bipWeightedCodegree H q x y|≤2*L^2*d := by
  have hp (u : B) := unit_product_deletion
    (bipAdj_nonneg H' x u) (bipAdj_subrelation H H' hsub x u) (bipAdj_le_one H x u)
    (bipAdj_nonneg H' y u) (bipAdj_subrelation H H' hsub y u) (bipAdj_le_one H y u)
  have he : bipWeightedCodegree H q x y-bipWeightedCodegree H' q x y=
      ∑ u,(bipAdj H x u*bipAdj H y u-bipAdj H' x u*bipAdj H' y u)*(q u)^2 := by
    simp only [sub_mul,bipWeightedCodegree,Finset.sum_sub_distrib]
  have hn : 0≤bipWeightedCodegree H q x y-bipWeightedCodegree H' q x y := by
    rw [he];exact Finset.sum_nonneg (fun u _=>mul_nonneg (hp u).1 (sq_nonneg _))
  rw [abs_sub_comm,abs_of_nonneg hn,he]
  calc
    _ ≤ ∑ u,((bipAdj H x u-bipAdj H' x u)+(bipAdj H y u-bipAdj H' y u))*L^2 := by
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul (hp u).2 (pow_le_pow_left₀ (hq u).1 (hq u).2 2)
        (sq_nonneg _) (le_trans (hp u).1 (hp u).2)
    _ ≤ 2*L^2*d := by
      simp only [bipAdj_deletion H H' hsub,← Finset.sum_mul,Finset.sum_add_distrib]
      have hh : (∑ u,bipAdj (fun x u=>H x u ∧ ¬H' x u) x u)+
          (∑ u,bipAdj (fun x u=>H x u ∧ ¬H' x u) y u)≤2*d := by linarith only [hd x,hd y]
      nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg L)]

end Oberwolfach
