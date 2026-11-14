module

public import Mathlib.Tactic

@[expose] public section
/-! Fix the matching robustness and an admissible vortex cap before the
later active tolerance and sampling rate, without linking robustness to the
sampling rate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_early_alpha_vortex_cap
    (b ρ₀ δglobal lamList βfinal εcap:ℝ)
    (hb:0<b) (hρ:0<ρ₀) (hδ:0<δglobal) (hlist:0<lamList)
    (hβ:0≤βfinal) (hβbound:βfinal≤lamList/4) (hcap:0<εcap):
    ∃α εupper:ℝ,0<α ∧ (2*α)/16≤b ∧ 2*α≤4*δglobal ∧
      0<εupper ∧ εupper≤εcap ∧ εupper≤δglobal ∧ βfinal+εupper≤lamList ∧
      εupper≤α/1000 ∧ εupper≤(ρ₀/4)/80000 ∧ εupper≤((ρ₀/4)/40000)/8192 :=by
  let α:ℝ:=min (4*b) δglobal
  have hα:0<α:=by dsimp [α];positivity
  have hαb:α≤4*b:=min_le_left _ _
  have hαδ:α≤δglobal:=min_le_right _ _
  let εupper:ℝ:=min εcap (min (δglobal/2) (min (lamList/2) (min (α/2000) (((ρ₀/4)/40000)/16384))))
  have he:0<εupper:=by dsimp [εupper];positivity
  have hecap:εupper≤εcap:=min_le_left _ _
  have heδ:εupper≤δglobal/2:=(min_le_right _ _).trans (min_le_left _ _)
  have helist:εupper≤lamList/2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have heα:εupper≤α/2000:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heρ:εupper≤((ρ₀/4)/40000)/16384:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨α,εupper,hα,by linarith,by linarith,he,hecap,by linarith,by linarith,by linarith,by linarith,by linarith⟩
end Oberwolfach
