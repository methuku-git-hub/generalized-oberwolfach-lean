module

public import Oberwolfach.OrdinaryTriangleParentBalance

@[expose] public section
/-! Turn a vortex degree profile and the original density identity into the
rim/spoke target needed on a fixed inner pair. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_parent_cross_target
    (degree reference pR pH hubs δ:ℝ) (hpR:0≤pR) (hpR1:pR≤1) (hδ:0≤δ)
    (hprofile:|degree-reference|≤δ) (hidentity:pR*reference=2*pH*hubs):
    |pR*degree-2*pH*hubs|≤δ:=by
  have hh:=mul_le_mul_of_nonneg_left hprofile hpR
  have he:pR*degree-2*pH*hubs=pR*(degree-reference):=by rw [←hidentity];ring
  rw [he,abs_mul,abs_of_nonneg hpR]
  have hs:=mul_le_mul_of_nonneg_right hpR1 hδ
  nlinarith only [hh,hs]
end Oberwolfach
