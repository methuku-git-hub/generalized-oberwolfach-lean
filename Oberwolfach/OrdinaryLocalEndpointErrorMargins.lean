module

public import Oberwolfach.OrdinaryLocalEndpointSizesFromCleanup

@[expose] public section
/-! Linear inner-scale edit and concentration errors fit the endpoint
row, column and codegree tolerances once the classes have relative size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_endpoint_error_margins
    (a η:ℝ) (ha:0<a) (hη:0<η):
    ∃δ:ℝ,0<δ ∧ ∀(A T pH tR tH L Rsize Hsize:ℝ),
      0≤A→A≤T→0≤pH→pH≤1→0≤tR→0≤tH→0≤L→
      tR+L≤δ*A→tH+L≤δ*A→a*T≤Rsize→a*T≤Hsize→
      (tH+2*L)+pH*(tH+L)≤η*Hsize ∧
      (tR+2*L)+pH*(tR+L)≤η*Rsize ∧
      (tH+3*L)+pH^2*(tH+L)≤η*Hsize:=by
  let δ:ℝ:=η*a/4
  have hδ:0<δ:=by dsimp [δ];positivity
  refine ⟨δ,hδ,?_⟩
  intro A T pH tR tH L Rsize Hsize hA hAT hpH hpH1 htR htH hL heR heH hRsize hHsize
  have hT:0≤T:=hA.trans hAT
  have hmeanR:a*A≤Rsize:=(mul_le_mul_of_nonneg_left hAT ha.le).trans hRsize
  have hmeanH:a*A≤Hsize:=(mul_le_mul_of_nonneg_left hAT ha.le).trans hHsize
  have hηR:η*(a*A)≤η*Rsize:=mul_le_mul_of_nonneg_left hmeanR hη.le
  have hηH:η*(a*A)≤η*Hsize:=mul_le_mul_of_nonneg_left hmeanH hη.le
  have hpR:pH*(tR+L)≤tR+L:=by nlinarith [mul_le_mul_of_nonneg_right hpH1 (add_nonneg htR hL)]
  have hpT:pH*(tH+L)≤tH+L:=by nlinarith [mul_le_mul_of_nonneg_right hpH1 (add_nonneg htH hL)]
  have hp2:pH^2≤1:=by nlinarith [sq_nonneg (1-pH)]
  have hpT2:pH^2*(tH+L)≤tH+L:=by nlinarith [mul_le_mul_of_nonneg_right hp2 (add_nonneg htH hL)]
  have hδA:4*(δ*A)=η*(a*A):=by dsimp [δ];ring
  constructor
  · nlinarith only [heH,hL,htH,hpT,hηH,hδA]
  constructor
  · nlinarith only [heR,hL,htR,hpR,hηR,hδA]
  · nlinarith only [heH,hL,htH,hpT2,hηH,hδA]
end Oberwolfach
