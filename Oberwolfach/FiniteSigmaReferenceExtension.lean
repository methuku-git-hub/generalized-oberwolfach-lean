module

public import Oberwolfach.FiniteSigmaPositiveExtension

@[expose] public section
/-! Use an existence theorem that accepts any high-probability retained event
to select a joint outcome satisfying the retained reference and joint event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_sigma_reference_extension
    {Ω Λ:Type} [Fintype Ω] [Fintype Λ] {F:Λ→Type} [∀ y,Fintype (F y)]
    (μ:FiniteLaw Ω) (f:Ω→Λ) (ν:∀ y,FiniteLaw (F y))
    (B:(Σ x,F (f x))→Prop) (Ref:(Σ y,F y)→Prop) (p:ℝ):
    let joint:=μ.sigma (fun x=>ν (f x))
    let selected:=(μ.map f).sigma ν
    let project:=fun z:(Σ x,F (f x))=>(⟨f z.1,z.2⟩:(Σ y,F y));
    p≤joint.probability B→
    (∀ E:(Σ y,F y)→Prop,p≤selected.probability E→∃ y,Ref y ∧ E y)→
    ∃ z,Ref (project z) ∧ B z ∧ 0<joint.mass z:=by
  intro joint selected project hB hRef
  let Extra:=fun y:(Σ y,F y)=>∃ z,project z=y ∧ B z ∧ 0<joint.mass z
  have hprob:p≤selected.probability Extra:=
    hB.trans (finiteLaw_sigma_positive_extension_probability μ f ν B)
  obtain ⟨y,hy,z,hproject,hgood,hmass⟩:=hRef Extra hprob
  refine ⟨z,?_,hgood,hmass⟩
  simpa only [hproject] using hy
end Oberwolfach
