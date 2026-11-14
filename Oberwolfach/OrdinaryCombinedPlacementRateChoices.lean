module

public import Oberwolfach.OrdinaryPairCapacityLoadRateChoices
public import Oberwolfach.OrdinaryMatchingMassRateChoices

@[expose] public section
/-! One ordered choice meets the pair-label, residual-capacity, bad-graph
load, full-mass error and residual-size budgets simultaneously. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_combined_placement_rate_choices
    (m:ℕ) (θ δ:ℝ) (hθ:0<θ) (hδ:0<δ) (hθδ:θ≤δ/8):
    ∃D:ℕ,∀d≥D,0<d ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧
      ∀a:ℝ,0<a→∃κ b ζ matchErr:ℝ,
        0<κ ∧ 0<b ∧ 0<ζ ∧ 0<matchErr ∧ b≤a/16 ∧ b≤δ/4 ∧
        16/(d:ℝ)+16*κ+16*b/a≤θ/8 ∧
        2*θ+δ/8+((m:ℝ)+2)*κ≤δ ∧
        1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζ+matchErr≤(δ/8)/2:=by
  obtain ⟨D₀,hD₀⟩:=ordinary_pair_capacity_and_load_rate_choices θ δ hθ hδ
  obtain ⟨D₁,hD₁⟩:=ordinary_matching_mass_rate_choices m (δ/8) (by positivity)
  refine ⟨max D₀ D₁,?_⟩
  intro d hd
  obtain ⟨hd0,hspace,hrates⟩:=hD₀ d (by omega)
  obtain ⟨_,ζ,matchErr,hζ,he,hMass⟩:=hD₁ d (by omega)
  refine ⟨hd0,hspace,?_⟩
  intro a ha
  obtain ⟨κ₀,b,hκ₀,hb,hba,hbδ,hcap⟩:=hrates a ha
  let κ:=min κ₀ (δ/(8*((m:ℝ)+2)))
  have hm:0<(m:ℝ)+2:=by positivity
  have hκ:0<κ:=lt_min hκ₀ (by positivity)
  have hκ0:κ≤κ₀:=min_le_left _ _
  have hκδ:κ≤δ/(8*((m:ℝ)+2)):=min_le_right _ _
  have hκterm:((m:ℝ)+2)*κ≤δ/8:=by
    have hh:=mul_le_mul_of_nonneg_left hκδ hm.le
    have heq:((m:ℝ)+2)*(δ/(8*((m:ℝ)+2)))=δ/8:=by field_simp <;> ring
    rw [heq] at hh
    exact hh
  refine ⟨κ,b,ζ,matchErr,hκ,hb,hζ,he,hba,hbδ,?_,?_,hMass⟩
  · linarith
  · linarith
end Oberwolfach
