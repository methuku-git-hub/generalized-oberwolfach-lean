module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! Local spoke changes fit an active-set cap when the retention and
unassigned errors are measured on the first vortex, and the remaining
terms are chosen relative to its already fixed size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_active_local_spoke_budget
    (cap θ ζ N I W P L err defect:ℝ)
    (hcap:0≤cap) (hI:0≤I) (hN:N≤2*I) (hW:3*I/4≤W)
    (hθ:θ≤cap/128) (hζ:ζ≤cap/128)
    (hP:P≤cap*N/128) (hL:2*L≤cap*N/128)
    (herr:err≤cap*N/128) (hdefect:defect≤cap*N/128):
    (ζ*I+P+2*L)+(2*θ*I+err+2*ζ*I+defect)≤cap*W :=by
  have ht:=mul_le_mul_of_nonneg_right hθ hI
  have hz:=mul_le_mul_of_nonneg_right hζ hI
  have hn:=mul_le_mul_of_nonneg_left hN hcap
  have hw:=mul_le_mul_of_nonneg_left hW hcap
  nlinarith only [ht,hz,hn,hw,hP,hL,herr,hdefect,mul_nonneg hcap hI]
end Oberwolfach
