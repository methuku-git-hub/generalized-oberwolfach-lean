module

public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.RawRetentionProjection

@[expose] public section

/-! Exact projection of a dependent second-stage experiment. The second
law depends on the projected first-stage outcome; no independence between
that second stage and the first is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_sigma_projection_probability {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    {F : Λ→Type*} [∀ a,Fintype (F a)] (μ : FiniteLaw Ω) (f : Ω→Λ)
    (ν : ∀ a,FiniteLaw (F a)) (E : (Σ a,F a)→Prop) :
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E ⟨f z.1,z.2⟩)=
      ((μ.map f).sigma ν).probability E := by
  rw [finiteLaw_sigma_probability,finiteLaw_sigma_probability,finiteLaw_map_expectation]

theorem finiteLaw_pi_sigma_injective_projection
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {State : I→Type*} [∀ i,Fintype (State i)]
    (μ : ∀ i,FiniteLaw (State i)) (f : J→I) (hf : Function.Injective f)
    {F : (∀ j,State (f j))→Type*} [∀ σ,Fintype (F σ)]
    (ν : ∀ σ,FiniteLaw (F σ)) (E : (Σ σ,F σ)→Prop) :
    ((FiniteLaw.pi μ).sigma (fun σ=>ν (fun j=>σ (f j)))).probability
      (fun z=>E ⟨fun j=>z.1 (f j),z.2⟩)=
      ((FiniteLaw.pi (fun j=>μ (f j))).sigma ν).probability E := by
  rw [finiteLaw_sigma_projection_probability,finiteLaw_pi_injective_projection μ f hf]

end Oberwolfach
