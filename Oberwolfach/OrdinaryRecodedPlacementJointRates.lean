module

public import Oberwolfach.OrdinaryPlacementOriginalSpacingRates
public import Oberwolfach.OrdinaryActualPhysicalRateBudget

@[expose] public section
/-! Shrink the forced-placement error to fit the already selected extending
list deletion budget, while retaining all matching capacity inequalities. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_recoded_placement_rates_with_list_deletion
    (m d:ℕ) (hd:0<d) (θ δ α ζList:ℝ)
    (hθ:0<θ) (hθsmall:θ≤1/100) (hδ:0<δ) (hθδ:θ≤δ/8) (hα:0<α) (hζList:0<ζList)
    (hspace:1/(4*(d:ℝ))≤5*θ^2/256):
    ∃κ b z ζret matchErr σ:ℝ,0<κ ∧ 0<b ∧ 0<z ∧ 0<ζret ∧ 0<matchErr ∧ 0<σ ∧
      b≤ζList ∧ b≤α/16 ∧ b≤δ/8 ∧ z≤b/4 ∧
      16/(d:ℝ)+16*κ+16*b/α+4*z≤θ/8 ∧
      2*θ+δ/8+((m:ℝ)+2)*κ≤δ ∧
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+matchErr≤(δ/8)/2 ∧
    ∀(n edit inner reserve conflict:ℝ),0≤n→
      edit≤σ*n→inner≤σ*n→ reserve≤σ*n→conflict≤σ*n→
      edit+2*inner+reserve+conflict≤b*n :=by
  obtain ⟨κ,b₀,z₀,ζret,matchErr,hκ,hb₀,hz₀,hζret,he,hba,hbδ,hcap,hsize,hmass⟩:=
    ordinary_forced_placement_rates_from_abundance_spacing m d hd θ δ α hθ hθsmall hδ hθδ hα hspace
  let b:ℝ:=min b₀ ζList
  let z:ℝ:=min z₀ (b/8)
  have hb:0<b:=by dsimp [b];positivity
  have hz:0<z:=by dsimp [z];positivity
  have hb0:b≤b₀:=min_le_left _ _
  have hbList:b≤ζList:=min_le_right _ _
  have hz0:z≤z₀:=min_le_left _ _
  have hzb:z≤b/8:=min_le_right _ _
  have hbdiv:b/α≤b₀/α:=div_le_div_of_nonneg_right hb0 hα.le
  have hcmp:16*b/α≤16*b₀/α:=div_le_div_of_nonneg_right (by linarith [hb0]) hα.le
  have hcap':16/(d:ℝ)+16*κ+16*b/α+4*z≤θ/8:=by
    linarith only [hcap,hcmp,hz0]
  obtain ⟨σ,hσ,hσbudget⟩:=ordinary_matching_degree_rate_choice b hb
  refine ⟨κ,b,z,ζret,matchErr,σ,hκ,hb,hz,hζret,he,hσ,hbList,hb0.trans hba,hb0.trans hbδ,?_,hcap',hsize,hmass,hσbudget⟩
  linarith
end Oberwolfach
