module

public import Oberwolfach.BipartiteIntersectionEstimates
public import Oberwolfach.AlternatingCombinations

@[expose] public section

/-! The concrete rectangle averaging operator, retaining all four
adjacency conditions and the supplied inverse density profile. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def sparseRectangleCoefficient (H : A → B → Prop) (q : B → ℝ) (z : A×B → ℝ)
    (x y : A) (u v : B) : ℝ :=
  (bipAdj H x u*bipAdj H y u*bipAdj H y v*bipAdj H x v)*
    (z (x,u)*q u*(q v)^2)/((Fintype.card A:ℝ)*Fintype.card B)

def sparseAlternatingMap (H : A → B → Prop) (q : B → ℝ) :
    (A×B → ℝ) →ₗ[ℝ] (A×B → ℝ) where
  toFun z := rectangleCombination (sparseRectangleCoefficient H q z)
  map_add' z w := by
    ext e
    simp only [rectangleCombination,sparseRectangleCoefficient,Pi.add_apply,add_mul,mul_add,add_div,
      Finset.sum_add_distrib]
  map_smul' c z := by
    ext e
    simp only [rectangleCombination,sparseRectangleCoefficient,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl;intro x _
    apply Finset.sum_congr rfl;intro y _
    apply Finset.sum_congr rfl;intro u _
    apply Finset.sum_congr rfl;intro v _
    ring

theorem sparseRectangleCoefficient_supported (H : A → B → Prop) (q : B → ℝ) (z : A×B → ℝ)
    (x y : A) (u v : B) (h : sparseRectangleCoefficient H q z x y u v≠0) :
    H x u ∧ H y u ∧ H y v ∧ H x v := by
  unfold sparseRectangleCoefficient bipAdj at h
  split_ifs at h <;> simp_all

theorem sparseAlternatingMap_zero_marginals (H : A → B → Prop) (q : B → ℝ) (z : A×B → ℝ) :
    sparseAlternatingMap H q z∈zeroMarginalSpace H :=
  rectangleCombination_zero_marginals H _ (sparseRectangleCoefficient_supported H q z)

def sparseOppositeMap (H : A → B → Prop) (q : B → ℝ) :
    (A×B → ℝ) →ₗ[ℝ] (A×B → ℝ) where
  toFun z e := bipAdj H e.1 e.2*(q e.2)^2/((Fintype.card A:ℝ)*Fintype.card B)*
    (∑ y,∑ v,bipAdj H e.1 v*bipAdj H y e.2*q v*z (y,v))
  map_add' z w := by
    ext e
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c z := by
    ext e
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl;intro y _
    apply Finset.sum_congr rfl;intro v _
    ring

theorem bipAdj_mul_supported (H : A → B → Prop) (z : A×B → ℝ)
    (hz : ∀ x u,¬H x u → z (x,u)=0) (x : A) (u : B) :
    bipAdj H x u*z (x,u)=z (x,u) := by
  unfold bipAdj
  split_ifs with h
  · simp
  · simp [hz x u h]

theorem sparseAlternatingMap_entry (H : A → B → Prop) (q : B → ℝ) (z : A×B → ℝ)
    (hz : ∀ x u,¬H x u → z (x,u)=0) (x : A) (u : B) (hxu : H x u) :
    sparseAlternatingMap H q z (x,u)=
      z (x,u)*q u/((Fintype.card A:ℝ)*Fintype.card B)*
        (∑ y,bipAdj H y u*bipWeightedCodegree H q x y)-
      q u/((Fintype.card A:ℝ)*Fintype.card B)*
        (∑ y,z (y,u)*bipWeightedCodegree H q x y)+sparseOppositeMap H q z (x,u)-
      (q u)^2/((Fintype.card A:ℝ)*Fintype.card B)*
        (∑ v,z (x,v)*q v*bipPairIntersection H v u) := by
  change rectangleCombination _ (x,u)=_
  rw [rectangleCombination_entry]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hadj : bipAdj H x u=1 := if_pos hxu
  have hfirst : (∑ y,∑ v,sparseRectangleCoefficient H q z x y u v)=
      z (x,u)*q u/((Fintype.card A:ℝ)*Fintype.card B)*
        (∑ y,bipAdj H y u*bipWeightedCodegree H q x y) := by
    unfold sparseRectangleCoefficient bipWeightedCodegree
    simp only [hadj,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro y _
    apply Finset.sum_congr rfl;intro v _
    ring
  have hsecond : (∑ y,∑ v,sparseRectangleCoefficient H q z y x u v)=
      q u/((Fintype.card A:ℝ)*Fintype.card B)*
        (∑ y,z (y,u)*bipWeightedCodegree H q x y) := by
    unfold sparseRectangleCoefficient bipWeightedCodegree
    simp only [hadj,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro y _
    apply Finset.sum_congr rfl;intro v _
    calc
      _ = (bipAdj H y u*z (y,u))*
        (q u*(bipAdj H x v*bipAdj H y v*(q v)^2)/((Fintype.card A:ℝ)*Fintype.card B)) := by ring
      _ = _ := by rw [bipAdj_mul_supported H z hz];ring
  have hthird : (∑ y,∑ v,sparseRectangleCoefficient H q z y x v u)=
      sparseOppositeMap H q z (x,u) := by
    change _=bipAdj H x u*(q u)^2/((Fintype.card A:ℝ)*Fintype.card B)*_
    unfold sparseRectangleCoefficient
    simp only [hadj,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro y _
    apply Finset.sum_congr rfl;intro v _
    calc
      _ = (bipAdj H y v*z (y,v))*
        (bipAdj H x v*bipAdj H y u*q v*(q u)^2/((Fintype.card A:ℝ)*Fintype.card B)) := by ring
      _ = _ := by rw [bipAdj_mul_supported H z hz];ring
  have hfourth : (∑ y,∑ v,sparseRectangleCoefficient H q z x y v u)=
      (q u)^2/((Fintype.card A:ℝ)*Fintype.card B)*
        (∑ v,z (x,v)*q v*bipPairIntersection H v u) := by
    rw [Finset.sum_comm]
    unfold sparseRectangleCoefficient bipPairIntersection
    simp only [hadj,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro v _
    apply Finset.sum_congr rfl;intro y _
    calc
      _ = (bipAdj H x v*z (x,v))*
        (bipAdj H y v*bipAdj H y u*q v*(q u)^2/((Fintype.card A:ℝ)*Fintype.card B)) := by ring
      _ = _ := by rw [bipAdj_mul_supported H z hz];ring
  rw [hfirst,hsecond,hthird,hfourth]

end Oberwolfach
