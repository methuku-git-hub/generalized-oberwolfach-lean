module

public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! Preserve all tests of the structural core in the input order required
    by the named parent selector, without changing the probability bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_structural_core_original_selector_probability
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω)
    (Prior Parent Expanded Stable Correction Good Reserve Concrete Boundary Relative:Ω→Prop) (b:ℝ):
    b≤μ.probability (fun z=>(Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧
      Good z ∧ Reserve z ∧ Concrete z ∧ Boundary z) ∧ Relative z)→
    b≤μ.probability (fun z=>(Prior z ∧ Expanded z ∧ Stable z ∧ Reserve z ∧ Relative z) ∧
      Parent z ∧ True ∧ Correction z ∧ Good z ∧ Concrete z ∧ Boundary z) :=by
  intro hprob
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  rcases hz with ⟨⟨hp,hparent,hexp,hstable,hcorr,hgood,hreserve,hconcrete,hboundary⟩,hrelative⟩
  exact ⟨⟨hp,hexp,hstable,hreserve,hrelative⟩,hparent,True.intro,hcorr,hgood,hconcrete,hboundary⟩
end Oberwolfach
