module

public import Oberwolfach.MarkedReferenceParentLoadFromZeroDeletionSplit

@[expose] public section
/-! Numerical choices for the parent-level adaptive load error. This does
not assert the sampling event or the parent weight hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem marked_reference_parent_load_margin_choice (r:ℕ) (κ ρstar sstar Bload Kload:ℝ)
    (hκ:0<κ) (hρ:0<ρstar) (hs:0<sstar) (hB:0<Bload) (hK:0<Kload):
    ∃ τ εLoad ζLoad:ℝ,0<τ ∧ 0<εLoad ∧ 0<ζLoad ∧
      τ+εLoad+11*(((r+4):ℝ)+1)^4*(2*Bload/(ρstar*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*Kload*ζLoad≤κ/4 := by
  let C:ℝ:=11*(((r+4):ℝ)+1)^4*(2*Bload/(ρstar*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*Kload
  have hC:0<C:=by dsimp [C];positivity
  refine ⟨κ/16,κ/16,κ/(16*(C+1)),by positivity,by positivity,by positivity,?_⟩
  have hden:0<16*(C+1):=by positivity
  have hfrac:C*(κ/(16*(C+1)))≤κ/16:=by
    apply (le_div_iff₀ (by norm_num: (0:ℝ)<16)).2
    have hratio:C/(C+1)≤1:=(div_le_one (by positivity)).2 (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hratio hκ.le
    have hid:(C*(κ/(16*(C+1))))*16=κ*(C/(C+1)):=by field_simp <;> ring
    rw [hid]
    linarith
  change κ/16+κ/16+C*(κ/(16*(C+1)))≤κ/4
  linarith
end Oberwolfach
