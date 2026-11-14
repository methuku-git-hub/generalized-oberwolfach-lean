module

public import Oberwolfach.OrdinaryTriangleSeparatedNumericScales

@[expose] public section
/-! Once the vortex shrinkage is fixed, the independent prescribed load can
be chosen small enough that the root cover costs a prescribed fraction of the
next vortex level. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_separated_cover_rate
    (ε δ cap:ℝ) (hε:0<ε) (hδ:0<δ) (hcap:0<cap) (hεsmall:ε≤δ/12):
    ∃a:ℝ,0<a ∧ a≤cap ∧ ∀N I T W:ℝ,0≤N→0≤I→0≤T→0≤W→
      ε*N/2≤I→T≤ε*I→W≤ε*I→
      18*a*N+3*(W+T)≤δ*I ∧ 9*a*N+3*T≤δ*I :=by
  let a:ℝ:=min cap (δ*ε/72)
  have ha:0<a:=lt_min hcap (by positivity)
  have hacap:a≤cap:=min_le_left _ _
  have hasmall:a≤δ*ε/72:=min_le_right _ _
  refine ⟨a,ha,hacap,?_⟩
  intro N I T W hN hI hT hW hsize hTsmall hWsmall
  have hload:18*a*N≤δ*I/2:=by
    have hh:=mul_le_mul_of_nonneg_right hasmall hN
    have hh':=mul_le_mul_of_nonneg_left hsize hδ.le
    nlinarith only [hh,hh']
  have hroot:3*(W+T)≤δ*I/2:=by
    have hh:=mul_le_mul_of_nonneg_right hεsmall hI
    nlinarith only [hTsmall,hWsmall,hh]
  have hload0:0≤a*N:=mul_nonneg ha.le hN
  have hW0:0≤W:=hW
  constructor <;> nlinarith only [hload,hroot,hload0,hW0]
end Oberwolfach
