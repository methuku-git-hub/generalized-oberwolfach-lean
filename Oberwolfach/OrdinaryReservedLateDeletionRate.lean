module

public import Oberwolfach.OrdinaryActualPhysicalRateBudget

@[expose] public section
/-! After spacing and the matching robustness tolerance are known, shrink
the physical-edit rate without invalidating earlier placement margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_reserved_late_deletion_rate
    (α b z cap:ℝ) (hα:0<α) (hb:0<b) (hz:0<z) (hcap:0<cap):
    ∃b' z' σ:ℝ,0<b' ∧ 0<z' ∧ 0<σ ∧ b'≤b ∧ b'≤cap ∧ z'≤z ∧ z'≤b'/4 ∧
      (∀(n edit inner reserve conflict:ℝ),0≤n→
        edit≤σ*n→inner≤σ*n→ reserve≤σ*n→conflict≤σ*n→
        edit+2*inner+reserve+conflict≤b'*n) ∧
      ∀(d θ κ:ℝ),16/d+16*κ+16*b/α+4*z≤θ/8→
        16/d+16*κ+16*b'/α+4*z'≤θ/8 :=by
  let b':ℝ:=min b cap
  let z':ℝ:=min z (b'/8)
  have hb':0<b':=by dsimp [b'];positivity
  have hz':0<z':=by dsimp [z'];positivity
  have hbb:b'≤b:=min_le_left _ _
  have hbc:b'≤cap:=min_le_right _ _
  have hzz:z'≤z:=min_le_left _ _
  have hzb:z'≤b'/8:=min_le_right _ _
  obtain ⟨σ,hσ,hbudget⟩:=ordinary_matching_degree_rate_choice b' hb'
  refine ⟨b',z',σ,hb',hz',hσ,hbb,hbc,hzz,by linarith,hbudget,?_⟩
  intro d θ κ hOld
  have hdiv:b'/α≤b/α:=div_le_div_of_nonneg_right hbb hα.le
  have hmul:16*b'/α≤16*b/α:=by
    have heq:16*b'/α=16*(b'/α):=by ring
    have heq':16*b/α=16*(b/α):=by ring
    rw [heq,heq']
    linarith
  linarith
end Oberwolfach
