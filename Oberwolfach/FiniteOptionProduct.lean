module

public import Oberwolfach.CommonEvents
public import Oberwolfach.ConvexDistanceProjection
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

/-! Exact fibre disintegration of a finite product law. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

def configurationCons (a : Ω) (x : I → Ω) (i : Option I) : Ω :=
  Option.rec a (fun j=>x j) i

theorem finiteLaw_pi_option_expectation
    (μ : Option I → FiniteLaw Ω) (X : (Option I → Ω) → ℝ) :
    (FiniteLaw.pi μ).expectation X=
      (μ none).expectation (fun a=>
        (FiniteLaw.pi (fun i=>μ (some i))).expectation (fun x=>X (configurationCons a x))) := by
  classical
  unfold FiniteLaw.expectation
  rw [← (Equiv.piOptionEquivProd (β:=fun _ : Option I=>Ω)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [FiniteLaw.pi,Fintype.prod_option,Equiv.piOptionEquivProd,
    Equiv.coe_fn_symm_mk]
  rw [mul_assoc]
  rfl

theorem configurationFibre_mem (A : Finset (Option I → Ω)) (a : Ω) (x : I → Ω) :
    x∈configurationFibre A a ↔ configurationCons a x∈A := by
  classical
  constructor
  · intro hx
    obtain ⟨y,hy,ht⟩ := Finset.mem_image.mp hx
    obtain ⟨hyA,hya⟩ := Finset.mem_filter.mp hy
    have he : y=configurationCons a x := by
      funext i
      cases i with
      | none => exact hya
      | some i => exact congrFun ht i
    rwa [← he]
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨configurationCons a x,Finset.mem_filter.mpr ⟨hx,rfl⟩,rfl⟩

theorem configurationFibre_subset_projection
    (A : Finset (Option I → Ω)) (a : Ω) :
    configurationFibre A a⊆configurationProjection A :=
  Finset.image_subset_image (Finset.filter_subset _ _)

theorem finiteLaw_pi_option_probability
    (μ : Option I → FiniteLaw Ω) (A : Finset (Option I → Ω)) :
    (FiniteLaw.pi μ).probability (fun x=>x∈A)=
      (μ none).expectation (fun a=>
        (FiniteLaw.pi (fun i=>μ (some i))).probability
          (fun x=>x∈configurationFibre A a)) := by
  classical
  rw [finiteLaw_probability_eq_expectation,finiteLaw_pi_option_expectation]
  unfold FiniteLaw.expectation
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  dsimp only
  rw [finiteLaw_probability_eq_expectation]
  unfold FiniteLaw.expectation
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  simp only [configurationFibre_mem]

theorem finiteLaw_pi_projection_probability
    (μ : Option I → FiniteLaw Ω) (A : Finset (Option I → Ω)) :
    (FiniteLaw.pi μ).probability (fun x=>x∈A)≤
      (FiniteLaw.pi (fun i=>μ (some i))).probability
        (fun x=>x∈configurationProjection A) := by
  rw [finiteLaw_pi_option_probability]
  calc
    _ ≤ (μ none).expectation (fun _=>
      (FiniteLaw.pi (fun i=>μ (some i))).probability
        (fun x=>x∈configurationProjection A)) := by
      apply finiteLaw_expectation_mono
      intro a
      exact finiteLaw_probability_mono _ _ _ (fun x hx=>
        configurationFibre_subset_projection A a hx)
    _ = _ := finiteLaw_expectation_const _ _

end Oberwolfach
