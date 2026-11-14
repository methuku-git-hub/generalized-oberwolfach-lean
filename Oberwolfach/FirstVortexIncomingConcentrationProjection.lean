module

public import Oberwolfach.FirstVortexExpandedConcentrationProjection

@[expose] public section
/-! The first-vortex chain uses incoming orientation counts, together with
the unassigned-colour degree bound, from the same sampled event. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_incoming_concentration_projection
    {n:ℕ} (P:SimpleGraph (Fin n)) (σ:Sym2 (Fin n)→Fin 6×Bool)
    (p₁ k₁ p₂ k₂ u:ℝ)
    (h:∀(j:Fin 6) (v:Fin n),
      |((∑x,sampledColourOrientation P σ j v x:ℕ):ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ) ∧
      |((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ) ∧
      |(sampledColourDegree P (fun e=>(σ e).1) j v:ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j*P.degree v|<(n:ℝ)^(3/5:ℝ)):
    (∀j v,|((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
    (∀v,|(sampledColourDegree P (fun e=>(σ e).1) 4 v:ℝ)-u*P.degree v|≤(n:ℝ)^(3/5:ℝ)) :=by
  refine ⟨fun j v=>(h j v).2.1,?_⟩
  intro v
  have hh:=(h 4 v).2.2
  simpa [markedExpandedPhysicalProbability] using hh.le
end Oberwolfach
