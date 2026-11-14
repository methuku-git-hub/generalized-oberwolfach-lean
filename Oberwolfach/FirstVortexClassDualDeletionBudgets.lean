module

public import Oberwolfach.FirstVortexClassOrderedEditMargins

@[expose] public section
/-! Select the orientation correction and regular-class edit tolerances
before the order, with room in both deletion budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_class_dual_deletion_budgets
    (αHost αAssign ρ₀ ε Δ ξBudget δold δlocal lam lam₀:ℝ)
    (hαHost:0<αHost) (hαAssign:0<αAssign) (hρ₀:0<ρ₀) (hε:0<ε)
    (hΔ:0<Δ) (hξBudget:0<ξBudget) (hgap:δold<δlocal) (hlam:lam₀<lam):
    ∃δ:ℝ,0<δ ∧ ∀c:ℝ,0<c→∃ξPart:ℝ,0<ξPart ∧
      δ+ξPart≤Δ ∧ δ+ξPart≤ξBudget ∧
      ξPart≤min (min (c/4) (δ/16)) (αHost*(ρ₀/200)^2/4) ∧
      ξPart≤αAssign/32 ∧ ξPart/2≤(lam-lam₀)*ε ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
        (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),0<m→
        ξPart*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ):=by
  obtain ⟨δ,hδ,hchoose⟩:=first_vortex_class_ordered_edit_margins
    αHost αAssign ρ₀ ε (2*min Δ ξBudget) δold δlocal lam lam₀
    hαHost hαAssign hρ₀ hε (by positivity) hgap hlam
  refine ⟨δ,hδ,?_⟩
  intro c hc
  obtain ⟨ξPart,hξ,hbudget,hbound,hdegree,hedges,hload⟩:=hchoose c hc
  have hmin:δ+ξPart≤min Δ ξBudget:=by linarith
  exact ⟨ξPart,hξ,hmin.trans (min_le_left _ _),hmin.trans (min_le_right _ _),hbound,hdegree,hedges,hload⟩
end Oberwolfach
