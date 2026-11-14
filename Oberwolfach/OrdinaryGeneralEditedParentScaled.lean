module

public import Oberwolfach.OrdinaryGeneralEditedParentFromCommon
public import Oberwolfach.OrdinaryGeneralParentEditScaleChoice

@[expose] public section
/-! Choose the edited-parent tolerances before the host and derive all of
its numerical edit hypotheses from one local rate bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_edited_parent_scaled
    (m:ℕ) (hm:3≤m) (βH ηH B ω pstar ζcap:ℝ) (hβH:0<βH) (hηH:0<ηH) (hB:0≤B) (hω:0<ω) (hp:0<pstar) (hcap:0<ζcap):
    ∃βparent εparent ζ rate:ℝ,0<βparent ∧ 0<εparent ∧ 0<ζ ∧ 0<rate ∧ ζ≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N₀≤Fintype.card V→0<Fintype.card U→Fintype.card U≤Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀(d k:ℕ),4≤k→∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V)
      (α βP ηP row c pR pH h δ L:ℝ) (weight:OrdinaryCycle P (m+1)→ℝ) (s:U→Color→ℝ) (j:Color)
      (raw:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool),
    pstar≤pR→pR≤1→pstar≤pH→pH≤1→0≤c→0≤L→L≤rate*Fintype.card V→Q≤P\F→
    (∀C,c/(Fintype.card V:ℝ)^((m+1)-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^((m+1)-2))→
    ordinaryCombinedHostEvent m d k hm P F π (max (1/2) (cycleThreshold (m+1))) α pstar βP ηP row ηH βH c B pR pH weight s j raw→
    OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h raw coins→
    (∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)→
    (∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)→
    (∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)→
    Nonempty (OrdinaryEditedParentFields (m+1) (by omega) k α βparent c (B/(ω*pstar^(2*(m+1)-1))) (2*h-ζ) δ εparent P Q F H) :=by
  obtain ⟨βparent,εparent,ζ,rate,hβparent,hεparent,hζ,hrate,hζcap,hdegree,N₀,hN₀,hscales⟩:=
    ordinary_general_parent_edit_scale_choice (m+1) βH ηH B ω pstar ζcap hβH hηH hB hω hp hcap
  refine ⟨βparent,εparent,ζ,rate,hβparent,hεparent,hζ,hrate,hζcap,N₀,hN₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu hUhi hUlo d k hk P Q F H π α βP ηP row c pR pH h δ L weight s j raw coins
    hRlo hRhi hHlo hHhi hc hL hLrate hQP hw event cuts hR hRow hCol
  have hn0:0<Fintype.card V:=by omega
  have hN:(N₀:ℝ)≤Fintype.card V:=by exact_mod_cast hn
  obtain ⟨hscaleV,hscaleU,hI,hT,hweight⟩:=hscales (Fintype.card V) (Fintype.card U) L hN hUlo hL hLrate
  exact ordinary_general_edited_parent_from_common m d k hm hk P Q F H π α pstar βP ηP row ηH βH c B pR pH
    ω βparent h ζ δ εparent L weight s j raw coins hn0 hu hUhi hω hp hUlo hRlo hRhi hHlo hHhi hc hB hζ.le hL hQP
    hw event cuts hR hRow hCol hscaleV hscaleU hdegree hI hT hweight
end Oberwolfach
