module

public import Oberwolfach.SparseAlternatingOperator

@[expose] public section

/-! Exact composition of the opposite-corner operator. The triple
intersection appears after summing over the intermediate row. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def bipTripleKernel (H : A → B → Prop) (q : B → ℝ) (x : A) (u : B) (s : A) (t : B) : ℝ :=
  ∑ v,bipAdj H x v*bipAdj H s v*(q v)^3*bipTripleIntersection H u v t

theorem finite_double_sum_exchange (f : A → B → A → B → ℝ) :
    (∑ y,∑ v,∑ s,∑ t,f y v s t)=(∑ s,∑ t,∑ y,∑ v,f y v s t) := by
  have hh := Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)
    (f:=fun e : A×B=>fun e' : A×B=>f e.1 e.2 e'.1 e'.2)
  simpa only [Fintype.sum_prod_type] using hh

theorem sparseOppositeMap_square (H : A → B → Prop) (q : B → ℝ) (z : A×B → ℝ)
    (x : A) (u : B) :
    sparseOppositeMap H q (sparseOppositeMap H q z) (x,u)=
      bipAdj H x u*(q u)^2/((Fintype.card A:ℝ)^2*(Fintype.card B:ℝ)^2)*
        (∑ s,∑ t,z (s,t)*q t*bipTripleKernel H q x u s t) := by
  change bipAdj H x u*(q u)^2/((Fintype.card A:ℝ)*Fintype.card B)*
    (∑ y,∑ v,bipAdj H x v*bipAdj H y u*q v*
      (bipAdj H y v*(q v)^2/((Fintype.card A:ℝ)*Fintype.card B)*
        (∑ s,∑ t,bipAdj H y t*bipAdj H s v*q t*z (s,t))))=_
  unfold bipTripleKernel bipTripleIntersection
  simp only [Finset.mul_sum]
  rw [finite_double_sum_exchange]
  apply Finset.sum_congr rfl;intro s _
  apply Finset.sum_congr rfl;intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro v _
  apply Finset.sum_congr rfl;intro y _
  ring

end Oberwolfach
