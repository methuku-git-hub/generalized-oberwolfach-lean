module

public import Mathlib.Tactic

@[expose] public section
/-! Transport a pre-matching test-mass estimate to the actual matching count. -/
set_option autoImplicit false
namespace Oberwolfach

theorem weighted_matching_count_deviation
    (r mass actual target err γ:ℝ)
    (hr:0≤r) (hmass:0≤mass) (hγ:0≤γ)
    (hdev:|r*mass-target|≤err)
    (hlow:(1-γ)*mass≤actual) (hup:actual≤(1+γ)*mass):
    |r*actual-target|≤err+γ*(|target|+err):=by
  have habs:0≤|target|:=abs_nonneg _
  have htarget:target≤|target|:=le_abs_self target
  have hrmass:r*mass≤|target|+err:=by
    have hh:=(abs_le.mp hdev).2
    linarith
  have hm:0≤r*mass:=mul_nonneg hr hmass
  have hmul:γ*(r*mass)≤γ*(|target|+err):=mul_le_mul_of_nonneg_left hrmass hγ
  have hbound:|r*(actual-mass)|≤γ*(r*mass):=by
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hr (sub_nonneg.mpr hlow),mul_nonneg hr (sub_nonneg.mpr hup)]
  have htri:|r*actual-target|≤|r*(actual-mass)|+|r*mass-target|:=by
    have hh:=abs_add_le (r*(actual-mass)) (r*mass-target)
    convert hh using 1 <;> congr 1 <;> ring
  linarith
end Oberwolfach
