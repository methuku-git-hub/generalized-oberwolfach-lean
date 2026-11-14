module

public import Oberwolfach.MarkedVortexActiveTransferFromSmallerParent

@[expose] public section
/-! The parent event may be requested at a smaller positive tolerance so
its first-active configurations and rows meet the corrected transfer bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_parent_tolerance_for_active_transfer
    (r:ℕ) (βA βrec cycleCoeff pathCoeff ζCfg tstar upper:ℝ)
    (hζ:0<ζCfg) (ht:0<tstar) (hupper:0<upper) (hβ:βrec≤βA)
    (hcycle:3*βA≤cycleCoeff-(r+5:ℕ)*ζCfg)
    (hpath:3*βA≤pathCoeff-(r+4:ℕ)*ζCfg):
    ∃δparent:ℝ,0<δparent ∧ δparent≤upper ∧ 2*δparent≤ζCfg ∧
      δparent+δparent≤tstar/16 ∧
      3*βrec≤cycleCoeff-(r+5:ℕ)*(2*δparent) ∧
      3*βrec≤pathCoeff-(r+4:ℕ)*(2*δparent) :=by
  let δ:ℝ:=min upper (min (ζCfg/2) (tstar/32))/2
  have hδ:0<δ:=by dsimp [δ];positivity
  have hup:δ≤upper:=by dsimp [δ];have :=min_le_left upper (min (ζCfg/2) (tstar/32));linarith
  have hcfg:2*δ≤ζCfg:=by
    dsimp [δ]
    have hh: min upper (min (ζCfg/2) (tstar/32))≤ζCfg/2:=(min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hrow:δ+δ≤tstar/16:=by
    dsimp [δ]
    have hh: min upper (min (ζCfg/2) (tstar/32))≤tstar/32:=(min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hc:=mul_le_mul_of_nonneg_left hcfg (show (0:ℝ)≤(r+5:ℕ) by positivity)
  have hp:=mul_le_mul_of_nonneg_left hcfg (show (0:ℝ)≤(r+4:ℕ) by positivity)
  exact ⟨δ,hδ,hup,hcfg,hrow,by linarith,by linarith⟩
end Oberwolfach
