module

public import Oberwolfach.MarkedParentRefinedLevelMargins

@[expose] public section
/-! Before the sample, choose an early parent tolerance with simultaneous
reference, potential, endpoint and inner-cut slack. Later choices may shrink it. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_parent_early_tolerance_budget
    (r:ℕ) (κ theta x cutGap upper Cparent:ℝ)
    (hκ:0<κ) (hθ:0<theta) (hx:0<x) (hcut:0<cutGap) (hupper:0<upper) (hC:0≤Cparent):
    ∃δ₀:ℝ,0<δ₀ ∧ δ₀≤upper ∧
      δ₀+(r+12:ℕ)*δ₀≤κ/4 ∧
      δ₀+δ₀+Cparent*δ₀≤κ/4 ∧
      δ₀+δ₀+Cparent*δ₀≤theta/4 ∧
      δ₀+(r+12:ℕ)*δ₀≤x/2 ∧ δ₀≤cutGap :=by
  let N:ℝ:=1+((r+12:ℕ):ℝ)
  let C:ℝ:=2+Cparent
  have hN:0<N:=by dsimp [N];positivity
  have hC':0<C:=by dsimp [C];linarith
  let δ₀:ℝ:=min upper (min (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))))
  have hδ:0<δ₀:=by dsimp [δ₀];positivity
  have hu:δ₀≤upper:=by dsimp [δ₀];have :=min_le_left upper (min (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))));linarith
  have hNκ:δ₀≤κ/(4*N):=by
    dsimp [δ₀]
    have ha:=min_le_right upper (min (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))))
    have hb:=min_le_left (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap)))
    linarith
  have hCκ:δ₀≤κ/(4*C):=by
    dsimp [δ₀]
    have ha:=min_le_right upper (min (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))))
    have hb:=min_le_right (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap)))
    have hc:=min_le_left (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))
    linarith
  have hCθ:δ₀≤theta/(4*C):=by
    dsimp [δ₀]
    have ha:=min_le_right upper (min (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))))
    have hb:=min_le_right (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap)))
    have hc:=min_le_right (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))
    have hd:=min_le_left (theta/(4*C)) (min (x/(2*N)) cutGap)
    linarith
  have hNx:δ₀≤x/(2*N):=by
    dsimp [δ₀]
    have ha:=min_le_right upper (min (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))))
    have hb:=min_le_right (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap)))
    have hc:=min_le_right (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))
    have hd:=min_le_right (theta/(4*C)) (min (x/(2*N)) cutGap)
    have he:=min_le_left (x/(2*N)) cutGap
    linarith
  have hcut':δ₀≤cutGap:=by
    dsimp [δ₀]
    have ha:=min_le_right upper (min (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))))
    have hb:=min_le_right (κ/(4*N)) (min (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap)))
    have hc:=min_le_right (κ/(4*C)) (min (theta/(4*C)) (min (x/(2*N)) cutGap))
    have hd:=min_le_right (theta/(4*C)) (min (x/(2*N)) cutGap)
    have he:=min_le_right (x/(2*N)) cutGap
    linarith
  have hnκ:δ₀*(4*N)≤κ:=(le_div_iff₀ (by positivity:0<4*N)).mp hNκ
  have hcκ:δ₀*(4*C)≤κ:=(le_div_iff₀ (by positivity:0<4*C)).mp hCκ
  have hcθ:δ₀*(4*C)≤theta:=(le_div_iff₀ (by positivity:0<4*C)).mp hCθ
  have hnx:δ₀*(2*N)≤x:=(le_div_iff₀ (by positivity:0<2*N)).mp hNx
  refine ⟨δ₀,hδ,hu,?_,?_,?_,?_,hcut'⟩ <;> dsimp [N,C] at * <;> nlinarith only [hnκ,hcκ,hcθ,hnx]
end Oberwolfach
