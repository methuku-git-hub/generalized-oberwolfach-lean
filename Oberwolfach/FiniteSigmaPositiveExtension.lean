module

public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! A high-probability event in a joint experiment projects to selected
outcomes that admit an extension of positive joint mass. No independence
between the projected outcome and the extension is used. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_positive_extension_probability
    {Ω Λ:Type} [Fintype Ω] [Fintype Λ] (μ:FiniteLaw Ω) (f:Ω→Λ) (B:Ω→Prop):
    μ.probability B≤(μ.map f).probability (fun y=>∃ x,f x=y ∧ B x ∧ 0<μ.mass x):=by
  rw [finiteLaw_map_probability]
  unfold FiniteLaw.probability
  apply Finset.sum_le_sum
  intro x _
  by_cases hB:B x
  · by_cases hx:0<μ.mass x
    · have he:∃ z,f z=f x ∧ B z ∧ 0<μ.mass z:=⟨x,rfl,hB,hx⟩
      simp [hB,he]
    · have hz:μ.mass x=0:=le_antisymm (le_of_not_gt hx) (μ.nonneg x)
      simp [hB,hz]
  · by_cases he:∃ z,f z=f x ∧ B z ∧ 0<μ.mass z
    · simp [hB,he,μ.nonneg x]
    · simp [hB,he]

theorem finiteLaw_sigma_positive_extension_probability
    {Ω Λ:Type} [Fintype Ω] [Fintype Λ] {F:Λ→Type} [∀ y,Fintype (F y)]
    (μ:FiniteLaw Ω) (f:Ω→Λ) (ν:∀ y,FiniteLaw (F y))
    (B:(Σ x,F (f x))→Prop):
    let joint:=μ.sigma (fun x=>ν (f x))
    let project:=fun z:(Σ x,F (f x))=>(⟨f z.1,z.2⟩:(Σ y,F y));
    joint.probability B≤((μ.map f).sigma ν).probability
      (fun y=>∃ x,project x=y ∧ B x ∧ 0<joint.mass x):=by
  intro joint project
  have hh:=finiteLaw_positive_extension_probability joint project B
  rw [finiteLaw_map_probability] at hh
  have hp:=finiteLaw_sigma_projection_probability μ f ν
    (fun y=>∃ x,project x=y ∧ B x ∧ 0<joint.mass x)
  change joint.probability (fun z=>∃ x,project x=project z ∧ B x ∧ 0<joint.mass x)=_ at hp
  rw [← hp]
  exact hh
end Oberwolfach
