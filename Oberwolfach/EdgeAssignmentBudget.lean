module

public import Oberwolfach.PrescribedPositionOriginalBounds

@[expose] public section
/-! The manuscript's constants leave an available index after forbidden
labels, conflicting edges and saturated indices are excluded. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem edge_assignment_numeric_budget (a b n total K bad conflicts list:ℝ)
    (ha:0<a) (hn:0<n) (hb:0≤b) (hbsmall:b≤a/16)
    (hK:0<K) (hKbound:4*total/(a*n)≤K) (htotal:0≤total)
    (hbad:bad≤2*b*n) (hconflicts:conflicts≤2*b*n) (hlist:a*n≤list):
    bad+conflicts+total/K<list := by
  have han:0<a*n:=mul_pos ha hn
  have hratio:total/K≤a*n/4:=by
    apply (div_le_iff₀ hK).mpr
    have h1:= (div_le_iff₀ han).mp hKbound
    nlinarith
  have hbn:0≤b*n:=mul_nonneg hb hn.le
  have hbound:4*b*n≤a*n/4:=by
    have hh:=mul_le_mul_of_nonneg_right hbsmall hn.le
    nlinarith
  linarith
end Oberwolfach
