module

public import Oberwolfach.OrdinaryTriangleOriginalRootFreeCoherentActualSelection
public import Oberwolfach.OrdinaryTriangleHubEarlyChoiceBeforeFailure
public import Oberwolfach.OrdinaryFixedVortexNonrootNumericAt
public import Oberwolfach.OrdinaryFixedVortexNonrootNumericInputsLateLoad

@[expose] public section
/-! From the original positive parameters, choose the common host margin,
inner/root-free and outer triangle hub selectors, and fine-cover caps before
the vortex scale and failure allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_original_fine_and_root_free_selection
    (θ α₀ ρ₀ pstar ηP:ℝ)
    (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1) (hα₀:0<α₀)
    (hρ₀:0<ρ₀) (hpstar:0<pstar) (hpstar1:pstar≤1) (hηP:0<ηP):
    ∃α cInner CInner κ cOuter COuter hrefLocal δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<α ∧ α≤α₀ ∧ α≤1 ∧ max (1/2) (cycleThreshold 3)+α/4≤1 ∧
      0<cInner ∧ 0<CInner ∧ OrdinaryNamedTriangleInnerEndpointSelector (α/2) cInner CInner ∧
      OrdinaryTriangleOriginalRootFreeCoherentActualAtMargin pstar (ρ₀/8) α cInner CInner ρ₀ pstar ηP hpstar ∧
      0<κ ∧ κ≤1 ∧ κ≤ρ₀/8 ∧ 0<cOuter ∧ 0<COuter ∧
      OrdinaryTriangleHubEarlyBeforeFailure (α/2) ρ₀ pstar κ cOuter COuter ∧
      0<hrefLocal ∧ hrefLocal≤(min ((α/2)/4) (1/4:ℝ))*pstar/64 ∧
      0<δcut ∧ δcut<1/4 ∧ δcut≤min ((min ((α/2)/4) (1/4:ℝ))/32) (pstar/512) ∧
      0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧ 0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
      OrdinaryFixedVortexNonrootNumericAt ρ₀ pstar hrefLocal κ κ κ δcut ζcut εcut ζlimit εsample εvortex :=by
  obtain ⟨α,cInner,CInner,hα,hαsub,hα1,hmargin,hc,hC,hinner,hroot⟩:=
    ordinary_triangle_original_root_free_coherent_actual_selection θ α₀ ρ₀ pstar ηP pstar (ρ₀/8)
      hθhalf hθcycle hθ1 hα₀ hρ₀ hpstar hpstar1 hηP hpstar hpstar1 (by positivity)
  obtain ⟨κ,cOuter,COuter,hκ,hκ1,hκcap,hcOuter,hCOuter,houter⟩:=
    ordinary_triangle_hub_early_choice_before_failure (α/2) ρ₀ pstar (ρ₀/8)
      (by positivity) hρ₀ hpstar hpstar1 (by positivity)
  let αcut:ℝ:=min ((α/2)/4) (1/4:ℝ)
  let hrefLocal:ℝ:=αcut*pstar/128
  let δlimit:ℝ:=min (αcut/32) (pstar/512)
  have hαcut:0<αcut:=by dsimp [αcut];positivity
  have hhref:0<hrefLocal:=by dsimp [hrefLocal];positivity
  have hδlimit:0<δlimit:=by dsimp [δlimit];positivity
  have hhrefcap:hrefLocal≤αcut*pstar/64:=by
    dsimp [hrefLocal];nlinarith [mul_pos hαcut hpstar]
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζcut,hεcut,hζlimit,hεsample,hεv,hεvsmall,hnum⟩:=
    ordinary_fixed_vortex_nonroot_numeric_inputs_late_load ρ₀ pstar hrefLocal δlimit κ κ κ hρ₀ hpstar hhref hδlimit hκ hκ hκ
  exact ⟨α,cInner,CInner,κ,cOuter,COuter,hrefLocal,δcut,ζcut,εcut,ζlimit,εsample,εvortex,
    hα,hαsub,hα1,hmargin,hc,hC,hinner,hroot,hκ,hκ1,hκcap,hcOuter,hCOuter,houter,
    hhref,hhrefcap,hδ,hδsmall,hδcap,hζcut,hεcut,hζlimit,hεsample,hεv,hεvsmall,hnum⟩
end Oberwolfach
