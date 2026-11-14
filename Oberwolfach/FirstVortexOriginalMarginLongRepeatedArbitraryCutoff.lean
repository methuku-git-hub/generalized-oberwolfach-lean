module

public import Oberwolfach.FirstVortexLongArbitraryCutoffMonotone

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_original_margin_long_repeated_factor_arbitrary_cutoff (α:ℝ) (hα:0<α) (KExtra:ℕ) :
    ∃K N:ℕ,KExtra≤K ∧ 3≤K ∧ ∀n≥N,∀(G:SimpleGraph (Fin n)) (D:ℕ),G.IsRegularOfDegree D→Even D→
      ∀F₀:SimpleGraph (Fin n),F₀.IsRegularOfDegree 2→∀Allowed:Set ℕ,
      Allowed.Nonempty→(∀s∈Allowed,3≤s)→AllowedCycleLengths F₀ Allowed→factorPreparationClass F₀ K=none→
      (allowedThreshold Allowed+α/2)*n≤(D:ℝ)→
      HasFactorDecomposition G (fun _:Fin (D/2)=>F₀) :=by
  exact first_vortex_long_arbitrary_cutoff_monotone α hα KExtra
end Oberwolfach
