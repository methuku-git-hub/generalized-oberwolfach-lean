module

public import Oberwolfach.OrdinaryWeightedCorrectionAfterLocalThresholds

@[expose] public section
/-! Choose the three first-level test thresholds and the global threshold
after fixing the positive failure allowances. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_weighted_correction_choose_local_thresholds
    (r d:ℕ) (hd:2 ≤ d) (mAbs a b t f q₀ N:ℕ) (α pstar ω εabs εv L ξ:ℝ)
    (hselect:OrdinaryWeightedCorrectionAfterTerminal r d hd mAbs a b t f q₀ N α pstar ω εabs εv L ξ)
    (ζlocal χlocal χglobal χhub χcol C:ℝ)
    (hζ:0<ζlocal) (hlocal:0<χlocal) (hglobal:0<χglobal) (hhub:0<χhub) (hcol:0<χcol) (hC:0 ≤ C):
    ∃Nc Ng Nh Ncol:ℕ,1 ≤ Nc ∧ 1 ≤ Ng ∧ 1 ≤ Nh ∧ 1 ≤ Ncol ∧
      OrdinaryWeightedCorrectionAfterLocalThresholds r d hd mAbs a b t f q₀ N Nc Ng Nh Ncol
        α pstar ω εabs εv L ξ ζlocal χlocal χglobal χhub χcol C :=by
  exact hselect ζlocal χlocal χglobal χhub χcol C hζ hlocal hglobal hhub hcol hC
end Oberwolfach
