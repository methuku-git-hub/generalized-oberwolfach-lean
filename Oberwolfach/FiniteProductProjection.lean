module

public import Oberwolfach.ResourcePatternConcentration
public import Oberwolfach.FiniteLawMap
public import Oberwolfach.InterfaceFamilyRegularization
public import Oberwolfach.ConditionalRealization

@[expose] public section

/-! Restriction of independent primitive coordinates to any fixed injective
subfamily preserves its exact product law. No conditioning is involved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_pi_injective_projection
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {State : I → Type*} [∀ i,Fintype (State i)]
    (μ : ∀ i,FiniteLaw (State i)) (f : J → I) (hf : Function.Injective f) :
    (FiniteLaw.pi μ).map (fun σ j=>σ (f j))=FiniteLaw.pi (fun j=>μ (f j)) := by
  apply finiteLaw_ext
  intro τ
  have hh := finiteLaw_disjoint_supported_family μ (fun j=>{f j})
    (fun j σ=>σ (f j)=τ j)
    (by intro j σ ρ ha;rw [ha (f j) (Finset.mem_singleton_self _)])
    Finset.univ (by
      intro i _ j _ hne
      simpa only [Finset.disjoint_singleton] using (fun h=>hne (hf h)))
  simp only [Finset.mem_univ,true_implies] at hh
  simp_rw [finiteLaw_pi_coordinate_probability] at hh
  simpa only [FiniteLaw.probability,FiniteLaw.map,FiniteLaw.pi,funext_iff] using hh

theorem finiteLaw_pi_injective_projection_event
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {State : I → Type*} [∀ i,Fintype (State i)]
    (μ : ∀ i,FiniteLaw (State i)) (f : J → I) (hf : Function.Injective f)
    (A : (∀ j,State (f j)) → Prop) :
    (FiniteLaw.pi μ).probability (fun σ=>A (fun j=>σ (f j)))=
      (FiniteLaw.pi (fun j=>μ (f j))).probability A := by
  rw [← finiteLaw_map_probability,finiteLaw_pi_injective_projection μ f hf]

end Oberwolfach
