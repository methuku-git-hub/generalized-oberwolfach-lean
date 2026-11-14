module

public import Oberwolfach.MarkedReferenceParentLoadMargin

@[expose] public section
/-! Simultaneous numerical margins for the parent and local marked loads. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem marked_joint_load_margin_choice (κ θ C D:ℝ)
    (hκ:0<κ) (hθ:0<θ) (hC:0≤C) (hD:0≤D):
    ∃ τ ε ζ ζlocal:ℝ,0<τ ∧ 0<ε ∧ 0<ζ ∧ 0<ζlocal ∧
      τ+ε+C*ζ≤κ/4 ∧ τ+ε+D*ζlocal≤θ/4 := by
  let t:ℝ:=min κ θ/16
  let z:ℝ:=κ/(16*(C+1))
  let w:ℝ:=θ/(16*(D+1))
  have ht:0<t:=by dsimp [t];have hh:0<min κ θ:=lt_min hκ hθ;positivity
  have hz:0<z:=by dsimp [z];positivity
  have hw:0<w:=by dsimp [w];positivity
  have htk:t≤κ/16:=by dsimp [t]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have htt:t≤θ/16:=by dsimp [t]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hcz:C*z≤κ/16:=by
    have hratio:C/(C+1)≤1:=(div_le_one (by linarith)).2 (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hratio hκ.le
    have hid:C*z=κ*(C/(C+1))/16:=by dsimp [z]; field_simp <;> ring
    rw [hid]
    linarith
  have hdw:D*w≤θ/16:=by
    have hratio:D/(D+1)≤1:=(div_le_one (by linarith)).2 (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hratio hθ.le
    have hid:D*w=θ*(D/(D+1))/16:=by dsimp [w]; field_simp <;> ring
    rw [hid]
    linarith
  refine ⟨t,t,z,w,ht,ht,hz,hw,?_,?_⟩ <;> linarith
end Oberwolfach
