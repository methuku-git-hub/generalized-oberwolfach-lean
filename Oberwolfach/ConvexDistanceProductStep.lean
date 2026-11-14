module

public import Oberwolfach.FiniteOptionProduct
public import Oberwolfach.ConvexDistanceFibreMoment

@[expose] public section

/-! The induction step in Talagrand's convex-distance inequality for
finite product measures. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

theorem finiteLaw_positive_finset_nonempty
    {Γ : Type*} [Fintype Γ] (μ : FiniteLaw Γ) (A : Finset Γ)
    (hA : 0<μ.probability (fun x=>x∈A)) : A.Nonempty := by
  by_contra h
  have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simp [he,FiniteLaw.probability] at hA

theorem finiteLaw_convexDistance_product_step
    (μ : Option I → FiniteLaw Ω)
    (ih : ∀ B : Finset (I → Ω),
      0<(FiniteLaw.pi (fun i=>μ (some i))).probability (fun x=>x∈B) →
      (FiniteLaw.pi (fun i=>μ (some i))).expectation (fun x=>Real.exp (convexDistanceSq B x/4))≤
        ((FiniteLaw.pi (fun i=>μ (some i))).probability (fun x=>x∈B))⁻¹)
    (A : Finset (Option I → Ω))
    (hA : 0<(FiniteLaw.pi μ).probability (fun x=>x∈A)) :
    (FiniteLaw.pi μ).expectation (fun x=>Real.exp (convexDistanceSq A x/4))≤
      ((FiniteLaw.pi μ).probability (fun x=>x∈A))⁻¹ := by
  classical
  let ν := FiniteLaw.pi (fun i=>μ (some i))
  let B := configurationProjection A
  let p := ν.probability (fun x=>x∈B)
  let q := (FiniteLaw.pi μ).probability (fun x=>x∈A)
  let f : Ω → ℝ := fun a=>ν.probability (fun x=>x∈configurationFibre A a)
  have hp : 0<p := hA.trans_le (finiteLaw_pi_projection_probability μ A)
  have hq : 0<q := hA
  have hAne := finiteLaw_positive_finset_nonempty (FiniteLaw.pi μ) A hA
  have hB := ih B hp
  have hf (a : Ω) : f a≤p := finiteLaw_probability_mono ν _ _
    (fun x hx=>configurationFibre_subset_projection A a hx)
  have hf0 (a : Ω) : 0≤f a := finiteLaw_probability_nonneg ν _
  have hfibre (a : Ω) :
      ν.expectation (fun x=>Real.exp (convexDistanceSq A (configurationCons a x)/4))≤
        (2-f a/p)/p := by
    by_cases ha : 0<f a
    · have hF := finiteLaw_positive_finset_nonempty ν (configurationFibre A a) ha
      apply finiteLaw_convexDistance_fibre_moment ν
        (fun x=>convexDistanceSq (configurationFibre A a) x/4)
        (fun x=>convexDistanceSq B x/4)
        (fun x=>convexDistanceSq A (configurationCons a x)/4)
        ha (hf a) (ih _ ha) hB
      intro θ hθ0 hθ1 x
      have hh := convexDistanceSq_fibre_mix A (configurationCons a x) hF hθ0 hθ1
      change convexDistanceSq A (configurationCons a x)≤
        θ*convexDistanceSq (configurationFibre A a) x+
          (1-θ)*convexDistanceSq B x+(1-θ)^2 at hh
      linarith
    · have hzero : f a=0 := le_antisymm (le_of_not_gt ha) (hf0 a)
      rw [hzero,zero_div,sub_zero]
      apply finiteLaw_convexDistance_empty_fibre_moment ν
        (fun x=>convexDistanceSq B x/4)
        (fun x=>convexDistanceSq A (configurationCons a x)/4) hp hB
      intro x
      have hh := convexDistanceSq_projection A hAne (configurationCons a x)
      change convexDistanceSq A (configurationCons a x)≤convexDistanceSq B x+1 at hh
      linarith
  have hfmean : (μ none).expectation f=q := (finiteLaw_pi_option_probability μ A).symm
  have hmean : (μ none).expectation (fun a=>(2-f a/p)/p)=(2-q/p)/p := by
    rw [← hfmean]
    unfold FiniteLaw.expectation
    have he (a : Ω) :
        (μ none).mass a*((2-f a/p)/p)=
          (μ none).mass a*(2/p)-((μ none).mass a*f a)/(p*p) := by ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.sum_div,(μ none).total,one_mul]
    ring
  have hfinal : (2-q/p)/p≤q⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hq).mpr
    have hp2 : 0<p*p := mul_pos hp hp
    have hs := sq_nonneg (p-q)
    have he : ((2-q/p)/p)*q=(2*p*q-q*q)/(p*p) := by field_simp <;> ring
    rw [he]
    apply (div_le_one hp2).mpr
    nlinarith
  calc
    _ = (μ none).expectation (fun a=>
      ν.expectation (fun x=>Real.exp (convexDistanceSq A (configurationCons a x)/4))) :=
        finiteLaw_pi_option_expectation _ _
    _ ≤ (μ none).expectation (fun a=>(2-f a/p)/p) :=
      finiteLaw_expectation_mono _ _ _ hfibre
    _ = _ := hmean
    _ ≤ _ := hfinal

end Oberwolfach
