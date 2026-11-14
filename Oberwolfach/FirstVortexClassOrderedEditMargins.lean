module

public import Oberwolfach.FirstVortexMatchingScalePositive
public import Oberwolfach.FirstClassMatchingRetargetScales
public import Oberwolfach.FirstClassRetargetLoadMargin
public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! The class-edit tolerance is chosen after the matching and correction
budgets and automatically fits the first vortex's local load margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_class_ordered_edit_margins
    (αHost αAssign ρ₀ ε Δ δold δlocal lam lam₀:ℝ)
    (hαHost:0<αHost) (hαAssign:0<αAssign) (hρ₀:0<ρ₀) (hε:0<ε)
    (hΔ:0<Δ) (hgap:δold<δlocal) (hlam:lam₀<lam):
    ∃δ:ℝ,0<δ ∧ ∀c:ℝ,0<c→∃ξ:ℝ,0<ξ ∧ δ+ξ≤Δ/2 ∧
      ξ≤min (min (c/4) (δ/16)) (αHost*(ρ₀/200)^2/4) ∧
      ξ≤αAssign/32 ∧ ξ/2≤(lam-lam₀)*ε ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
        (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),0<m→
        ξ*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ):=by
  obtain ⟨δ,hδ,hchoose⟩:=first_class_matching_retarget_scales
    αHost αAssign ρ₀ ε Δ (δlocal-δold) lam lam₀ hαHost hαAssign hρ₀ hε hΔ (sub_pos.mpr hgap) hlam
  refine ⟨δ,hδ,?_⟩
  intro c hc
  obtain ⟨ξ,hξ,hbudget,hbound,hdegree,hedges,hload⟩:=hchoose c hc
  refine ⟨ξ,hξ,hbudget,hbound,hdegree,hedges,?_⟩
  intro n U _ G D m β Q hm
  have hsize:ε*(n:ℝ)/2≤((Q.extendedVertices 1).card:ℝ):=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
  exact first_class_retarget_load_margin n (Q.extendedVertices 1).card ε ξ δold δlocal (sub_nonneg.mpr hgap.le) hsize hload
end Oberwolfach
