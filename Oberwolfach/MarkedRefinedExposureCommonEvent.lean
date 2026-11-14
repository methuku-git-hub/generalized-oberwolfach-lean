module

public import Oberwolfach.FiniteLawSigmaProjection
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! An additional event on a refined physical exposure can be intersected
with a selected-layer event while retaining the latter's exact marginal law. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_refined_exposure_common_event
    {Ω Λ:Type} [Fintype Ω] [Fintype Λ] {F:Λ→Type} [∀ a,Fintype (F a)]
    (μ:FiniteLaw Ω) (f:Ω→Λ) (ν:∀ a,FiniteLaw (F a))
    (E:(Σ a,F a)→Prop) (Extra:(Σ ω,F (f ω))→Prop) (a b:ℝ)
    (hE:1-a≤((μ.map f).sigma ν).probability E)
    (hExtra:1-b≤(μ.sigma (fun ω=>ν (f ω))).probability Extra):
    let law:=μ.sigma (fun ω=>ν (f ω));
    1-a-b≤law.probability (fun z=>E ⟨f z.1,z.2⟩ ∧ Extra z) ∧
    (a+b<1→∃ z,0<law.mass z ∧ E ⟨f z.1,z.2⟩ ∧ Extra z) := by
  intro law
  have hp:1-a≤law.probability (fun z=>E ⟨f z.1,z.2⟩):=by
    rw [finiteLaw_sigma_projection_probability]
    exact hE
  have hj:=finiteLaw_good_intersection law (fun z=>E ⟨f z.1,z.2⟩) Extra b hExtra
  have hbound:1-a-b≤law.probability (fun z=>E ⟨f z.1,z.2⟩ ∧ Extra z):=by linarith
  refine ⟨hbound,?_⟩
  intro hab
  let Good:=(fun z:Σ ω,F (f ω)=>E ⟨f z.1,z.2⟩ ∧ Extra z)
  letI : DecidablePred Good := fun z=>Classical.propDecidable (Good z)
  have hpos:0<law.probability Good:=by dsimp [Good];linarith
  unfold FiniteLaw.probability at hpos
  have hnonneg:∀ z∈Finset.univ,0≤(if Good z then law.mass z else 0):=by
    intro z _;split_ifs;exact law.nonneg z;norm_num
  obtain ⟨z,_,hz⟩:=(Finset.sum_pos_iff_of_nonneg hnonneg).mp hpos
  by_cases hzgood:Good z
  · exact ⟨z,by simpa [hzgood] using hz,hzgood⟩
  · simp [hzgood] at hz
end Oberwolfach
