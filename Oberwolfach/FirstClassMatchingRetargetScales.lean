module

public import Oberwolfach.FirstClassMatchingDistinctScales

@[expose] public section
/-! Choose the class edit after the matching and correction scales, also
reserving the local load margin needed to retarget the first source. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_class_matching_retarget_scales
    (αHost αAssign ρ₀ ε Δ δgap lam lam₀:ℝ)
    (hαHost:0<αHost) (hαAssign:0<αAssign) (hρ₀:0<ρ₀) (hε:0<ε)
    (hΔ:0<Δ) (hgap:0<δgap) (hlam:lam₀<lam):
    ∃δ:ℝ,0<δ ∧ ∀c:ℝ,0<c→∃ξ:ℝ,0<ξ ∧ δ+ξ≤Δ/2 ∧
      ξ≤min (min (c/4) (δ/16)) (αHost*(ρ₀/200)^2/4) ∧
      ξ≤αAssign/32 ∧ ξ/2≤(lam-lam₀)*ε ∧ ξ≤δgap*ε/2:=by
  obtain ⟨δ,hδ,hchoose⟩:=first_class_matching_distinct_ordered_scales αHost αAssign ρ₀ ε Δ lam lam₀
    hαHost hαAssign hρ₀ hε hΔ hlam
  refine ⟨δ,hδ,?_⟩
  intro c hc
  obtain ⟨ξ₀,hξ₀,hbudget,hbound,hdegree,hedges⟩:=hchoose c hc
  let ξ:=min ξ₀ (δgap*ε/2)
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hle:ξ≤ξ₀:=min_le_left _ _
  have hload:ξ≤δgap*ε/2:=min_le_right _ _
  refine ⟨ξ,hξ,?_,hle.trans hbound,hle.trans hdegree,?_,hload⟩
  · linarith
  · linarith
end Oberwolfach
