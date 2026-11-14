module

public import Oberwolfach.MarkedPreciseParentSharedErrorBudget

@[expose] public section
/-! Instantiate the shared parent error with the same weight and relative
active-size constants used in the selected parent event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_precise_parent_weighted_error_budget
    (r h:ℕ) (κ theta eta t x gapC gapP Bweight pstar ε:ℝ)
    (hκ:0<κ) (hθ:0<theta) (hη:0<eta) (ht:0<t) (hx:0<x)
    (hgapC:0<gapC) (hgapP:0<gapP) (hB:0≤Bweight) (hp:0<pstar) (he:0<ε):
    let C:=(((r+4:ℕ):ℝ)+1)^4*(2*Bweight/pstar^(2*(r+4)+1));
    ∃δ:ℝ,0<δ ∧
      δ+(r+12:ℕ)*δ≤κ/8 ∧
      δ+δ+11*C*δ≤κ/8 ∧ δ+δ+11*C*δ≤theta/8 ∧
      δ+δ+5*C*(4/ε)*δ≤eta/8 ∧ δ+δ≤t/16 ∧
      δ+h*δ≤x/4 ∧ (r+5:ℕ)*(2*δ)≤gapC ∧ (r+4:ℕ)*(2*δ)≤gapP :=by
  intro C
  have hC:0≤C:=by dsimp [C];positivity
  have hB':0≤C/ε:=div_nonneg hC he.le
  obtain ⟨δ,hδ,hcommon,hpot,hdeep,hactive,hrow,hboundary,hconfigC,hconfigP⟩:=
    marked_precise_parent_shared_error_budget r h κ theta eta t x gapC gapP C (C/ε) hκ hθ hη ht hx hgapC hgapP hC hB'
  refine ⟨δ,hδ,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · push_cast; nlinarith only [hcommon]
  · nlinarith only [hpot]
  · nlinarith only [hdeep]
  · have heq:δ+δ+5*C*(4/ε)*δ=(2+20*(C/ε))*δ:=by ring
    rw [heq]; exact hactive
  · nlinarith only [hrow]
  · push_cast; nlinarith only [hboundary]
  · push_cast; nlinarith only [hconfigC]
  · push_cast; nlinarith only [hconfigP]
end Oberwolfach
