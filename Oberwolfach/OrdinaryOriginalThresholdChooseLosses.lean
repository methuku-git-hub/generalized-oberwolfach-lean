module

public import Oberwolfach.OrdinaryOriginalThresholdAfterLosses

@[expose] public section
/-! Fix the probability tolerances while retaining the original weighted
selector for every sufficiently large graph and factor family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_original_threshold_choose_losses
    (rstar m k d K:ℕ) (hd:2 ≤ d) (βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel smin τ t ξ b:ℝ)
    (BO:Fin K → ℝ)
    (hchoice:OrdinaryOriginalThresholdAfterMatchChoice rstar m k d K hd βfreq ρ₀ α θ θhost
      lam aRow γ cap lamList ζDel smin τ t ξ b BO)
    (ζ χpair χlist σ χbal χbd χnbr χpairR χpath:ℝ)
    (hζ:0<ζ) (hχpair:0<χpair) (hχlist:0<χlist) (hσ:0<σ) (hχbal:0<χbal)
    (hχbd:0<χbd) (hχnbr:0<χnbr) (hχpairR:0<χpairR) (hχpath:0<χpath):
    OrdinaryOriginalThresholdAfterLosses rstar m k d K hd βfreq ρ₀ α θ θhost
      lam aRow γ cap lamList ζDel smin τ t ξ b BO ζ χpair χlist σ χbal χbd χnbr χpairR χpath :=by
  obtain ⟨_,_,_,_,_,_,_,_,_,hselect⟩:=hchoice
  exact hselect ζ χpair χlist σ χbal χbd χnbr χpairR χpath hζ hχpair hχlist hσ hχbal hχbd hχnbr hχpairR hχpath
end Oberwolfach
