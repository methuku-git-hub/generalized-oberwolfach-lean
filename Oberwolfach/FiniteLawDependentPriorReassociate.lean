module

public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Preserve a dependent prior, correction, matching and a derived reserve
when exposing the components required by a later continuation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_dependent_prior_reassociate
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω)
    (E Correction Matching Reserve Prior Parent Expanded Stable Concrete Boundary Relative:Ω→Prop)
    (hprior:∀x,E x→Prior x ∧ Parent x ∧ Expanded x ∧ Stable x ∧ Concrete x ∧ Boundary x ∧ Relative x)
    (b:ℝ)
    (hprob:b≤μ.probability (fun x=>((E x ∧ Correction x) ∧ Matching x) ∧ Reserve x)):
    b≤μ.probability (fun x=>E x ∧
      ((Prior x ∧ Parent x ∧ Expanded x ∧ Stable x ∧ Correction x ∧ Matching x ∧ Reserve x ∧
        Concrete x ∧ Boundary x) ∧ Relative x)) :=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro x hx
  obtain ⟨⟨⟨he,hc⟩,hm⟩,hr⟩:=hx
  obtain ⟨hp,hparent,hexp,hstable,hconcrete,hboundary,hrelative⟩:=hprior x he
  exact ⟨he,⟨⟨hp,hparent,hexp,hstable,hc,hm,hr,hconcrete,hboundary⟩,hrelative⟩⟩
end Oberwolfach
