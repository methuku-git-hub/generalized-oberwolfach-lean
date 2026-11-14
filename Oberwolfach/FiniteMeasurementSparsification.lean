module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic

@[expose] public section

/-! Caratheodory support reduction preserves every supplied measurement,
the total mass, and containment in the original positive support. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finite_measurement_sparsification
    {E J : Type} [Fintype E] [Fintype J] (z : E → J → ℝ) (w : E → ℝ)
    (hw : ∀ e,0≤w e) (hW : 0<∑ e,w e) :
    ∃ w' : E → ℝ,(∀ e,0≤w' e) ∧ (∀ e,w e=0 → w' e=0) ∧
      (∑ e,w' e=∑ e,w e) ∧ (∀ j,∑ e,w' e*z e j=∑ e,w e*z e j) ∧
      (Finset.univ.filter (fun e=>0<w' e)).card≤Fintype.card J+1 := by
  classical
  let W := ∑ e,w e
  have hW' : 0<W := hW
  let T := Finset.univ.filter (fun e=>0<w e)
  let x := ∑ e,(w e/W) • z e
  have hfilter : (∑ e∈T,w e/W)=1 := by
    dsimp only [T]
    rw [Finset.sum_filter]
    calc
      _ = ∑ e,w e/W := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : 0<w e
        · simp [he]
        · have hzero : w e=0 := le_antisymm (le_of_not_gt he) (hw e)
          simp [hzero]
      _ = 1 := by rw [← Finset.sum_div];exact div_self hW'.ne'
  have hxT : (∑ e∈T,(w e/W) • z e)=x := by
    dsimp only [T,x]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : 0<w e
    · simp [he]
    · have hzero : w e=0 := le_antisymm (le_of_not_gt he) (hw e)
      simp [hzero]
  have hx : x∈convexHull ℝ (z '' {e | 0<w e}) := by
    rw [← hxT]
    apply (convex_convexHull ℝ (z '' {e | 0<w e})).sum_mem
      (fun e _=>div_nonneg (hw e) hW'.le) hfilter
    intro e he
    exact subset_convexHull ℝ _ ⟨e,(Finset.mem_filter.mp he).2,rfl⟩
  obtain ⟨I,hI,z',a,hrange,haff,ha,hatotal,hxsum⟩ := eq_pos_convex_span_of_mem_convexHull hx
  letI := hI
  have hex : ∀ i : I,∃ e : E,0<w e ∧ z e=z' i := fun i=>hrange ⟨i,rfl⟩
  choose e he hze using hex
  let w' := fun f : E=>W*(∑ i : I,if e i=f then a i else 0)
  have hw' : ∀ f,0≤w' f := by
    intro f
    apply mul_nonneg hW'.le
    exact Finset.sum_nonneg (fun i _=>by split_ifs;exact (ha i).le;exact le_refl _)
  have hmass : (∑ f,w' f)=W := by
    dsimp only [w']
    rw [← Finset.mul_sum,Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,hatotal,mul_one]
  have hcoordinate (j : J) : ∑ f,w' f*z f j=∑ f,w f*z f j := by
    have hxj := congrFun hxsum j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,x] at hxj
    have htarget : W*(∑ i,a i*z' i j)=∑ f,w f*z f j := by
      rw [hxj,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      field_simp
    calc
      _ = W*(∑ i : I,a i*z (e i) j) := by
        dsimp only [w']
        simp only [mul_assoc,Finset.sum_mul,← Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      _ = W*(∑ i : I,a i*z' i j) := by simp only [hze]
      _ = _ := htarget
  have hsupport : Finset.univ.filter (fun f=>0<w' f)⊆Finset.univ.image e := by
    intro f hf
    by_contra hno
    have hall : ∀ i,e i≠f := by simpa only [Finset.mem_image,Finset.mem_univ,true_and,not_exists] using hno
    have hz : w' f=0 := by simp only [w',hall,ite_false,Finset.sum_const_zero,mul_zero]
    have hh := (Finset.mem_filter.mp hf).2
    rw [hz] at hh
    exact (lt_irrefl 0) hh
  have hcard : Fintype.card I≤Fintype.card J+1 := by
    have hh := haff.card_le_finrank_succ
    have hd := (vectorSpan ℝ (Set.range z')).finrank_le
    rw [Module.finrank_fintype_fun_eq_card] at hd
    omega
  refine ⟨w',hw',?_,hmass,hcoordinate,?_⟩
  · intro f hf
    have hall : ∀ i,e i≠f := by
      intro i hi
      have hh := he i
      rw [hi,hf] at hh
      exact (lt_irrefl 0) hh
    simp only [w',hall,ite_false,Finset.sum_const_zero,mul_zero]
  · exact (Finset.card_le_card hsupport).trans ((Finset.card_image_le).trans (by simpa only [Finset.card_univ] using hcard))

end Oberwolfach
