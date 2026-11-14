module

public import Oberwolfach.FiniteMeasurementSparsification
public import Oberwolfach.HypergraphWeightMoments

@[expose] public section

/-! Sparse weights retain the precise degree, pair and prescribed-test
measurements used by the manuscript's rounding lemma. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem fractional_resource_sparsification
    {V E A : Type} [Fintype V] [Fintype E] [Fintype A] [DecidableEq V]
    (R : E → Finset V) (w : E → ℝ) (g : A → E → ℝ)
    (hw : ∀ e,0≤w e) (hW : 0<∑ e,w e) :
    ∃ w' : E → ℝ,(∀ e,0≤w' e) ∧ (∀ e,w e=0 → w' e=0) ∧
      (∑ e,w' e=∑ e,w e) ∧
      (∀ v,hypergraphWeightedDegree R w' v=hypergraphWeightedDegree R w v) ∧
      (∀ u v,(∑ e,if u∈R e ∧ v∈R e then w' e else 0)=
        ∑ e,if u∈R e ∧ v∈R e then w e else 0) ∧
      (∀ i,∑ e,g i e*w' e=∑ e,g i e*w e) ∧
      (Finset.univ.filter (fun e=>0<w' e)).card≤
        Fintype.card V+Fintype.card V^2+Fintype.card A+1 := by
  classical
  let J := V ⊕ ((V×V)⊕A)
  let z : E → J → ℝ := fun e=>Sum.elim (fun v=>if v∈R e then 1 else 0)
    (Sum.elim (fun uv=>if uv.1∈R e ∧ uv.2∈R e then 1 else 0) (fun i=>g i e))
  obtain ⟨w',hw',hsupport,hmass,hmeasure,hcard⟩ := finite_measurement_sparsification z w hw hW
  refine ⟨w',hw',hsupport,hmass,?_,?_,?_,?_⟩
  · intro v
    simpa only [z,Sum.elim_inl,hypergraphWeightedDegree,mul_ite,mul_one,mul_zero] using hmeasure (Sum.inl v)
  · intro u v
    simpa only [z,Sum.elim_inr,Sum.elim_inl,mul_ite,mul_one,mul_zero] using hmeasure (Sum.inr (Sum.inl (u,v)))
  · intro i
    simpa only [z,Sum.elim_inr,mul_comm] using hmeasure (Sum.inr (Sum.inr i))
  · simpa only [J,Fintype.card_sum,Fintype.card_prod,pow_two,Nat.add_assoc] using hcard

theorem sum_floor_weighted_bounds
    {E : Type*} [Fintype E] (w g : E → ℝ) (T : ℕ) (b : ℝ)
    (hw : ∀ e,0≤w e) (hg : ∀ e,0≤g e ∧ g e≤b) :
    (T : ℝ)*(∑ e,g e*w e)-Fintype.card E*b≤∑ e,g e*⌊(T : ℝ)*w e⌋₊ ∧
    (∑ e,g e*⌊(T : ℝ)*w e⌋₊)≤(T : ℝ)*(∑ e,g e*w e) := by
  have hlow (e : E) : (T : ℝ)*(g e*w e)-b≤g e*⌊(T : ℝ)*w e⌋₊ := by
    have hf := Nat.lt_floor_add_one ((T : ℝ)*w e)
    have hm := mul_le_mul_of_nonneg_left hf.le (hg e).1
    nlinarith [ (hg e).2 ]
  have hupp (e : E) : g e*⌊(T : ℝ)*w e⌋₊≤(T : ℝ)*(g e*w e) := by
    have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg T) (hw e))
    have hm := mul_le_mul_of_nonneg_left hf (hg e).1
    nlinarith
  constructor
  · simpa only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      Finset.sum_le_sum (fun e (_ : e∈Finset.univ)=>hlow e)
  · simpa only [← Finset.mul_sum] using Finset.sum_le_sum (fun e (_ : e∈Finset.univ)=>hupp e)

end Oberwolfach
