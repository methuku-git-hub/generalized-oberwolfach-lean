module

public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! A two-stage pushforward with an outcome-dependent second-stage map. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_sigma_dependent_transport
    {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    {P : Ω → Type*} [∀ ω, Fintype (P ω)]
    {Q : Λ → Type*} [∀ y, Fintype (Q y)]
    (μ : FiniteLaw Ω) (ν : ∀ ω, FiniteLaw (P ω))
    (f : Ω → Λ) (τ : ∀ y, FiniteLaw (Q y))
    (T : ∀ ω, P ω → Q (f ω))
    (h : ∀ ω, (ν ω).map (T ω) = τ (f ω))
    (E : (Σ y, Q y) → Prop) :
    (μ.sigma ν).probability (fun z => E ⟨f z.1, T z.1 z.2⟩) =
      ((μ.map f).sigma τ).probability E := by
  rw [finiteLaw_sigma_probability, finiteLaw_sigma_probability, finiteLaw_map_expectation]
  apply congrArg (FiniteLaw.expectation μ)
  funext ω
  rw [← h ω, finiteLaw_map_probability]
end Oberwolfach
