module

public import Oberwolfach.MarkedVortexAbsorberCompatibleScales

@[expose] public section
/-! The shrinkage scale can be chosen before the weight-dependent
regularity tolerance; both remain compatible with the absorber. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_vortex_shrinkage_after_absorber (εAbs:ℝ) (hAbs:0<εAbs):
    ∃εQ:ℝ,0<εQ ∧ εQ<1/4 ∧ εQ≤εAbs := by
  let εQ:=min (1/8:ℝ) (εAbs/2)
  have he:0<εQ:=by dsimp [εQ];positivity
  have h1:εQ≤1/8:=min_le_left _ _
  have h2:εQ≤εAbs/2:=min_le_right _ _
  exact ⟨εQ,he,(by linarith),(by linarith)⟩

theorem marked_vortex_regularity_after_margins
    (α βmax εBal εRef:ℝ) (hα:0<α) (hβmax:0<βmax) (hBal:0<εBal) (hRef:0<εRef):
    ∃βQ:ℝ,0<βQ ∧ βQ≤1/4 ∧ βQ≤α/4 ∧ βQ≤βmax ∧ βQ≤εBal/4 ∧ βQ≤εRef/4 := by
  obtain ⟨εQ,βQ,he,he1,heAbs,hb,hb1,hbα,hbmax,hbbal,hbref⟩:=
    marked_vortex_absorber_compatible_scales α βmax εBal εRef 1 hα hβmax hBal hRef (by norm_num)
  exact ⟨βQ,hb,hb1,hbα,hbmax,hbbal,hbref⟩
end Oberwolfach
