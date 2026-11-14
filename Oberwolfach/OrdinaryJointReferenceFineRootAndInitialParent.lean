module

public import Oberwolfach.OrdinaryJointReferenceAndInitialParentLoadCapSelector
public import Oberwolfach.OrdinaryGeneralFineParentRootScaleChoice
public import Oberwolfach.OrdinaryGeneralEditScaleRateMonotone

@[expose] public section
/-! Select the all-level parent tests and the general-load sharp root from
one reference parameter family, retaining its allowable later edit rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_joint_reference_fine_root_and_initial_parent
    (m loadK d:ℕ) (hm:3≤m) (hd:2≤d) (α ρ₀ pstar ηP:ℝ)
    (hα:0<α) (hα1:α≤1/2)
    (hθ1:max (1/2) (cycleThreshold (m+1))+α/2≤1)
    (hρ₀:0<ρ₀) (hp:0<pstar) (hp1:pstar≤1) (hηP:0<ηP):
    ∃(δ h βP row:ℝ) (k:ℕ) (βH c B εstar cLinear:ℝ),
      0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<βP ∧ 0<row ∧ m+3≤k ∧
      0<βH ∧ 0<c ∧ 0<B ∧ 0<εstar ∧ 0<cLinear ∧
      OrdinaryGeneralDeepSafeCapacityRuleLinear m k hm α (ρ₀/16) (βH/8)
        (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2) εstar cLinear ∧
      OrdinarySharedInitialParentLoadCapJointSelectorAt m loadK d hm α k ∧
    ∀(ηH gap ζcap:ℝ),0<ηH→0<gap→0<ζcap→ζcap≤h→
    ∃ζparent rateParent lamroot:ℝ,0<ζparent ∧ 0<rateParent ∧ 0<lamroot ∧ ζparent≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
      OrdinaryGeneralEditScaleAt (m+1) βH ηH B (ρ₀/16) pstar (βH/2) (2*ηH) ζparent rateParent N₀ ∧
      OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad m k loadK (by omega) α (βH/2) c
        (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (2*h-ζparent) δ (2*ηH) (ρ₀/16) gap lamroot ∧
      (∀rate:ℝ,rate≤rateParent→OrdinaryGeneralEditScaleAt (m+1) βH ηH B (ρ₀/16) pstar
        (βH/2) (2*ηH) ζparent rate N₀) ∧
    ∀(ε χhost χcut:ℝ),0<ε→ε<1→0<χhost→0<χcut→
    ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
    ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pstar (ρ₀/16)
        βP ηP row ηH βH c B εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d)) :=by
  obtain ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,hjoint,hevents⟩:=
    ordinary_joint_reference_and_initial_parent_load_cap_selector m loadK d hm hd α ρ₀ pstar ηP hα hα1 hθ1 hρ₀ hp hp1 hηP
  refine ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,hjoint,?_⟩
  intro ηH gap ζcap hηH hgap hζcap hζh
  obtain ⟨ζparent,rateParent,lamroot,hζparent,hrate,hlam,hζcap',N₀,hN₀,hscale,hroot⟩:=
    ordinary_general_fine_parent_root_scale_choice m loadK k hm (by omega) α βH ηH c B (ρ₀/16) pstar δ h gap ζcap
      hβH hηH hc.le hB.le (by positivity) hp hδ (by linarith) hh hgap hζcap hζh
  refine ⟨ζparent,rateParent,lamroot,hζparent,hrate,hlam,hζcap',N₀,hN₀,hscale,hroot,?_,?_⟩
  · intro rate hrate
    exact ordinary_general_edit_scale_rate_monotone (m+1) βH ηH B (ρ₀/16) pstar (βH/2) (2*ηH) ζparent rate rateParent N₀ hrate hscale
  · intro ε χhost χcut hε hε1 hχhost hχcut
    exact hevents ηH ε χhost χcut hηH hε hε1 hχhost hχcut
end Oberwolfach
