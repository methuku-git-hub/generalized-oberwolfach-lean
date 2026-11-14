module

public import Oberwolfach.MarkedParentToleranceFullActiveMargins

@[expose] public section
/-! Refining the earlier parent tolerance by a factor of two gives the
half-scale parent record needed before transferring the corrected fields. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_parent_refined_level_margins
    (r:ℕ) (βA βrec cycleCoeff pathCoeff ζCfg tstar δ₀ κ thetaDeep eta Cparent Cwide:ℝ)
    (hζ:0<ζCfg) (ht:0<tstar) (hδ₀:0<δ₀) (hη:0<eta) (hCp:0≤Cparent) (hCw:0≤Cwide)
    (hβ:βrec≤βA) (hcycle:3*βA≤cycleCoeff-(r+5:ℕ)*ζCfg)
    (hpath:3*βA≤pathCoeff-(r+4:ℕ)*ζCfg)
    (hκ:δ₀+(r+12:ℕ)*δ₀≤κ/4)
    (hparentκ:δ₀+δ₀+Cparent*δ₀≤κ/4)
    (hparentθ:δ₀+δ₀+Cparent*δ₀≤thetaDeep/4):
    ∃δ:ℝ,0<δ ∧ δ≤δ₀ ∧ 2*δ≤ζCfg ∧ δ+δ≤tstar/16 ∧
      δ+δ+Cwide*δ≤eta/8 ∧
      δ+(r+12:ℕ)*δ≤κ/8 ∧ δ+δ+Cparent*δ≤κ/8 ∧
      δ+δ+Cparent*δ≤thetaDeep/8 ∧
      3*βrec≤cycleCoeff-(r+5:ℕ)*(2*δ) ∧
      3*βrec≤pathCoeff-(r+4:ℕ)*(2*δ) :=by
  obtain ⟨δ,hδ,hδup,hcfg,hrow,hwide,hcycle',hpath'⟩:=
    marked_parent_tolerance_full_active_margins r βA βrec cycleCoeff pathCoeff ζCfg tstar (δ₀/2) eta Cwide
      hζ ht (by positivity) hη hCw hβ hcycle hpath
  have hhalf:2*δ≤δ₀:=by linarith
  have hnat:=mul_le_mul_of_nonneg_left hhalf (show (0:ℝ)≤(r+12:ℕ) by positivity)
  have hparent:=mul_le_mul_of_nonneg_left hhalf hCp
  refine ⟨δ,hδ,by linarith,hcfg,hrow,hwide,?_,?_,?_,hcycle',hpath'⟩
  · nlinarith only [hhalf,hnat,hκ]
  · nlinarith only [hhalf,hparent,hparentκ]
  · nlinarith only [hhalf,hparent,hparentθ]
end Oberwolfach
