module

public import Oberwolfach.ResourceRoundingCounts

@[expose] public section

/-! Set-incidence sums and error transfer after a matching of rounded copies. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem unweighted_resource_set_sum {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (R : E → Finset V) (S : Finset V) :
    (∑ e,((R e∩S).card : ℝ))=∑ v∈S,(Fintype.card (HypergraphEdgesAt R v) : ℝ) := by
  have heq (v : V) : hypergraphWeightedDegree R (fun _=>1) v=
      (Fintype.card (HypergraphEdgesAt R v) : ℝ) := by
    simp only [hypergraphWeightedDegree,HypergraphEdgesAt,Fintype.card_subtype,Finset.card_filter]
    push_cast
    rfl
  simpa only [mul_one,heq] using resource_set_test_sum R (fun _=>1) S

theorem resource_set_sum_bounds {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (R : E → Finset V) (S : Finset V) (L U : ℝ)
    (hdegree : ∀ v,L≤(Fintype.card (HypergraphEdgesAt R v) : ℝ) ∧
      (Fintype.card (HypergraphEdgesAt R v) : ℝ)≤U) :
    L*S.card≤(∑ e,((R e∩S).card : ℝ)) ∧
      (∑ e,((R e∩S).card : ℝ))≤U*S.card := by
  rw [unweighted_resource_set_sum]
  constructor
  · simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using
      Finset.sum_le_sum (fun v (_ : v∈S)=>(hdegree v).1)
  · simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using
      Finset.sum_le_sum (fun v (_ : v∈S)=>(hdegree v).2)

theorem rounded_matching_lower_transfer {η T D X W S γ : ℝ}
    (hη : 0<η) (hηsmall : η≤1/100) (hγ : 10*η≤γ)
    (hT : 0<T) (hW : 0≤W) (hDlo : (1+η)*T≤D) (hDhi : D≤(1+2*η)*T)
    (hX : (1-2*η)*T*W≤X) (hmatch : |S-X/D|<η*X/D) :
    (1-γ)*W≤S := by
  have hD : 0<D := (mul_pos (by linarith) hT).trans_le hDlo
  have hX0 : 0≤X := (mul_nonneg (mul_nonneg (by linarith) hT.le) hW).trans hX
  have hlo := (abs_lt.mp hmatch).1
  have hS : (1-η)*X/D<S := by
    rw [show (1-η)*X/D=X/D-η*X/D by ring]
    linarith
  have hSX := (div_lt_iff₀ hD).mp hS
  have hS0 : 0<S := by
    apply lt_of_le_of_lt _ hS
    exact div_nonneg (mul_nonneg (by linarith) hX0) hD.le
  have hX' := mul_le_mul_of_nonneg_left hX (show 0≤1-η by linarith)
  have hDS := mul_le_mul_of_nonneg_right hDhi hS0.le
  have hcoef : (1-5*η)*(1+2*η)≤(1-η)*(1-2*η) := by nlinarith
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hT.le hW)
  have hbound : (1-5*η)*W≤S := by
    nlinarith [mul_pos (show 0<1+2*η by linarith) hT]
  have hg := mul_le_mul_of_nonneg_right hγ hW
  nlinarith

theorem rounded_matching_upper_transfer {η T D X W S : ℝ}
    (hη : 0≤η) (hT : 0<T) (hW : 0≤W) (hDlo : (1+η)*T≤D)
    (hX : X≤T*W) (hmatch : |S-X/D|<η*X/D) : S≤W := by
  have hD : 0<D := (mul_pos (by linarith) hT).trans_le hDlo
  have hu := (abs_lt.mp hmatch).2
  have hS : S<(1+η)*X/D := by
    rw [show (1+η)*X/D=X/D+η*X/D by ring]
    linarith
  have hSX := (lt_div_iff₀ hD).mp hS
  have hX' := mul_le_mul_of_nonneg_left hX (show 0≤1+η by linarith)
  have hDW := mul_le_mul_of_nonneg_right hDlo hW
  nlinarith

end Oberwolfach
