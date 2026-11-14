module

public import Oberwolfach.ConvexDistanceProductStep
public import Oberwolfach.ConvexDistanceReindex
public import Oberwolfach.FiniteExponential
public import Mathlib.Data.Fintype.Option

@[expose] public section

/-! Talagrand's convex-distance inequality for a finite product of finite
probability spaces. The proof is by induction on the coordinate set;
all fibre probabilities refer to the given product law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_convexDistance_mgf
    {I Ω : Type*} [Fintype I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (A : Finset (I → Ω))
    (hA : 0<(FiniteLaw.pi μ).probability (fun x=>x∈A)) :
    (FiniteLaw.pi μ).expectation (fun x=>Real.exp (convexDistanceSq A x/4))≤
      ((FiniteLaw.pi μ).probability (fun x=>x∈A))⁻¹ := by
  classical
  revert μ A
  refine Fintype.induction_empty_option
    (P:=fun J _=>∀ (ν : J → FiniteLaw Ω) (B : Finset (J → Ω)),
      0<(FiniteLaw.pi ν).probability (fun x=>x∈B) →
      (FiniteLaw.pi ν).expectation (fun x=>Real.exp (convexDistanceSq B x/4))≤
        ((FiniteLaw.pi ν).probability (fun x=>x∈B))⁻¹) ?_ ?_ ?_ I
  · intro J K _ e ih ν B hB
    letI : Fintype J := Fintype.ofEquiv K e.symm
    exact finiteLaw_convexDistance_reindex e ν (ih (fun i=>ν (e i))) B hB
  · intro ν B hB
    obtain ⟨x,hx⟩ := finiteLaw_positive_finset_nonempty (FiniteLaw.pi ν) B hB
    have hall (y : PEmpty → Ω) : y∈B := (Subsingleton.elim x y) ▸ hx
    have hd (y : PEmpty → Ω) : convexDistanceSq B y=0 :=
      convexDistanceSq_mem B (hall y)
    simp only [hd,zero_div,Real.exp_zero]
    rw [finiteLaw_expectation_const]
    simp [FiniteLaw.probability,FiniteLaw.pi,hall]
  · intro J _ ih ν B hB
    have he : (fun a b : Option J=>Classical.propDecidable (a=b))=
        (@Option.instDecidableEq J (Classical.decEq J)) := Subsingleton.elim _ _
    rw [he] at hB ⊢
    exact finiteLaw_convexDistance_product_step ν (ih (fun i=>ν (some i))) B hB

theorem finiteLaw_convexDistance_tail
    {I Ω : Type*} [Fintype I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (A : Finset (I → Ω)) (t : ℝ) :
    (FiniteLaw.pi μ).probability (fun x=>x∈A)*
      (FiniteLaw.pi μ).probability (fun x=>t≤convexDistanceSq A x)≤Real.exp (-t/4) := by
  classical
  let p := (FiniteLaw.pi μ).probability (fun x=>x∈A)
  have hp0 : 0≤p := finiteLaw_probability_nonneg _ _
  by_cases hp : 0<p
  · have hm := finiteLaw_convexDistance_mgf μ A hp
    have hm' : (FiniteLaw.pi μ).expectation (fun x=>Real.exp ((1/4)*convexDistanceSq A x))≤p⁻¹ := by
      simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using hm
    have ht := finiteLaw_exponential_markov (FiniteLaw.pi μ) (convexDistanceSq A) t
      (s:=(1/4 : ℝ)) (by norm_num)
    have he : -(1/4 : ℝ)*t=-t/4 := by ring
    rw [he] at ht
    calc
      _ ≤ p*(Real.exp (-t/4)*(FiniteLaw.pi μ).expectation
          (fun x=>Real.exp ((1/4)*convexDistanceSq A x))) :=
        mul_le_mul_of_nonneg_left ht hp.le
      _ ≤ p*(Real.exp (-t/4)*p⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hm' (Real.exp_pos _).le) hp.le
      _ = _ := by rw [mul_left_comm,mul_inv_cancel₀ hp.ne',mul_one]
  · have he : p=0 := le_antisymm (le_of_not_gt hp) hp0
    change p*_≤_
    rw [he,zero_mul]
    exact (Real.exp_pos _).le

end Oberwolfach
