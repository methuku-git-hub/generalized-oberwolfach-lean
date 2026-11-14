module

public import Oberwolfach.FirstVortexSelectorActualHostCoreEfficientTail

@[expose] public section
/-! The selector's single expanded-sample concentration event supplies the
orientation and colour-degree inputs of the later matching chain. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_expanded_concentration_projection
    {n:ℕ} (P:SimpleGraph (Fin n)) (σ:Sym2 (Fin n)→Fin 6×Bool)
    (p₁ k₁ p₂ k₂ u:ℝ)
    (h:∀(j:Fin 6) (x:Fin n),
      |((∑y,sampledColourOrientation P σ j x y:ℕ):ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j/2*P.degree x|<(n:ℝ)^(3/5:ℝ) ∧
      |((∑y,sampledColourOrientation P σ j y x:ℕ):ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j/2*P.degree x|<(n:ℝ)^(3/5:ℝ) ∧
      |(sampledColourDegree P (fun e=>(σ e).1) j x:ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j*P.degree x|<(n:ℝ)^(3/5:ℝ)):
    (∀j x,|((∑y,sampledColourOrientation P σ j x y:ℕ):ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j/2*P.degree x|<(n:ℝ)^(3/5:ℝ)) ∧
    (∀x,|(sampledColourDegree P (fun e=>(σ e).1) 4 x:ℝ)-u*P.degree x|≤(n:ℝ)^(3/5:ℝ)) :=by
  refine ⟨fun j x=>(h j x).1,?_⟩
  intro x
  have hh:=(h 4 x).2.2
  simpa [markedExpandedPhysicalProbability] using hh.le
end Oberwolfach
