module

public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! Rearrange the structural-core event for the direct reserve preparation
    bridge, preserving every common test and the original probability bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_structural_core_reserve_probability
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω)
    (Prior Parent Expanded Stable Correction Good Reserve Concrete Boundary Relative:Ω→Prop) (b:ℝ):
    b≤μ.probability (fun z=>(Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧
      Good z ∧ Reserve z ∧ Concrete z ∧ Boundary z) ∧ Relative z)→
    b≤μ.probability (fun z=>(Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧
      Good z ∧ Concrete z ∧ Relative z) ∧ Boundary z ∧ Reserve z) :=by
  intro hprob
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  rcases hz with ⟨⟨hp,hparent,hexp,hstable,hcorr,hgood,hreserve,hconcrete,hboundary⟩,hrelative⟩
  exact ⟨⟨hp,hparent,hexp,hstable,hcorr,hgood,hconcrete,hrelative⟩,hboundary,hreserve⟩
end Oberwolfach
