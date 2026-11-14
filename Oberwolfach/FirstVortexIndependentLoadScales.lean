module

public import Oberwolfach.MarkedLocalCorrectionScaleBudget

@[expose] public section
/-! The forced-image and tracked free-image budgets can be selected below
an arbitrary later cap, independently of the larger embedding-host error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_independent_load_scales
    (host cap β:ℝ) (hhost:0<host) (hcap:0<cap) (hβ:0<β):
    ∃δsmall κ θ:ℝ,0<δsmall ∧ 0<κ ∧ 0<θ ∧ δsmall≤host ∧
      10*θ≤δsmall ∧ 10*θ≤κ*(β/4) ∧ 2*(δsmall+κ)≤cap :=by
  let δsmall:=min host (cap/16)/2
  let κ:=cap/32
  let θ:=min (δsmall/20) (κ*β/80)
  have hδ:0<δsmall:=by dsimp [δsmall];positivity
  have hk:0<κ:=by dsimp [κ];positivity
  have ht:0<θ:=by dsimp [θ];positivity
  have hdhost:δsmall≤host:=by
    have hh:=min_le_left host (cap/16)
    dsimp [δsmall]
    linarith
  have hdcap:δsmall≤cap/16:=by
    have hh:=min_le_right host (cap/16)
    dsimp [δsmall]
    linarith
  have hθδ:θ≤δsmall/20:=min_le_left _ _
  have hθk:θ≤κ*β/80:=min_le_right _ _
  refine ⟨δsmall,κ,θ,hδ,hk,ht,hdhost,?_,?_,?_⟩
  · linarith
  · have hh:0≤κ*β:=mul_nonneg hk.le hβ.le
    nlinarith
  · dsimp [κ]
    linarith
end Oberwolfach
