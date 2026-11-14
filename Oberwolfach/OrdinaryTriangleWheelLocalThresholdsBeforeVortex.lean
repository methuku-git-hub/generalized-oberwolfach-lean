module

public import Oberwolfach.OrdinaryTriangleInitialLaterFineCoverSharedChoice
public import Oberwolfach.OrdinaryVortexSharpGeometryFromRatesUniformSpoke
public import Oberwolfach.OrdinaryTriangleEarlyBalanceSelectors

@[expose] public section
/-! After the common spacing is chosen, select every initial and later local
threshold before choosing the vortex size or the factor-dependent spoke rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_wheel_local_thresholds_before_vortex
    (d k:ℕ) (ρ₀ α pmin href κ δcut ζcut εcut ζlimit εsample εvortex ε:ℝ)
    (ξroot aLoad ηbal αcut pstar β ηProfile ζcert cBoundary δDeep rate ηInitial δInitial:ℝ)
    (cInitial δedit ηedit:ℝ)
    (hcallbacks:∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
      ∃mInitial mBalance:ℕ,1≤mInitial ∧ 1≤mBalance ∧
        OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin pmin ηInitial cBoundary δInitial d β mInitial ∧
        OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin pmin ηProfile ζcert cBoundary δDeep rate d 2 β C mBalance)
    (hmargins:∀β:ℝ,0≤β→β≤1/4→β≤δedit→∃mEdit Nedit:ℕ,1≤mEdit ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin pmin ε ηbal cInitial δedit ηedit β d mEdit Nedit)
    (hnum:OrdinaryFixedVortexNonrootNumericAt ρ₀ pmin href κ κ κ δcut ζcut εcut ζlimit εsample εvortex)
    (hρ₀:0<ρ₀) (hε:0<ε) (hεsmall:ε<1/4) (hεv:ε≤εvortex) (hδ:0<δcut) (hδsmall:δcut<1/4)
    (hξ:0<ξroot) (hξEq:ξroot=min (ε/200) (aLoad^2/160)) (ha:0<aLoad) (ha1:aLoad≤1)
    (hbal:0<ηbal) (hbalcap:ηbal≤δcut*(ρ₀/8)*ξroot/1000) (hηI:0<ηInitial) (hηIcap:ηInitial≤ηbal)
    (hβ:0≤β) (hβ1:β≤1/4) (hβInitial:β≤δInitial) (hβDeep:β≤δDeep) (hβEdit:β≤δedit)
    (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit)
    (hδlim:δcut≤min (αcut/32) (pstar/512)) (hhref:href≤αcut*pstar/64)
    (lam ξreserve γgeom edit p βe βh r:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout:ℝ)
    (hgeometry:OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap
      βout ξreserve ζout edit p ηpack εout γgeom)
    (hγ:0<γgeom) (hlam:0≤lam) (hlam1:lam≤1/4) (hlamρ:lam≤(ρ₀/8)/2)
    (hξreserve:0≤ξreserve) (hεξ:ε≤ξreserve/2) (hερ:ε≤ξreserve*(ρ₀/8)/2) (hεroot:2*ε^2≤lam)
    (hβe:0≤βe) (hβh:0≤βh) (hp:0≤p) (hr:0≤r) (hedit:0<edit)
    (hβcap:β≤γgeom/1000) (hrcap:r≤γgeom/1000) (hξcap:ξroot≤γgeom/160000)
    (haCap:aLoad≤γgeom/1000) (hbalCap:ηbal≤γgeom/1000)
    (hrow:3*lam≤edit/4) (hlevel:lam*3≤edit/4)
    (haEdit:aLoad≤edit/(72*((2:ℝ)+2))) (hlamE:lam≤βe/4) (hlamH:lam≤βh/2):
    ∃mInitial mBalance mEdit Nedit mFineInitial mFineLater mGeom mAll:ℕ,
      1≤mInitial ∧ 1≤mBalance ∧ 1≤mEdit ∧ 1≤mGeom ∧
      mInitial≤mAll ∧ mBalance≤mAll ∧ mEdit≤mAll ∧ mFineInitial≤mAll ∧ mFineLater≤mAll ∧ mGeom≤mAll ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin pmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin pmin ηProfile ζcert cBoundary δDeep rate d 2 β 0 mBalance ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin pmin ε ηbal cInitial δedit ηedit β d mEdit Nedit ∧
      OrdinaryInitialTriangleFineCoverFromSharedAt d ρ₀ pmin href κ δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar β mFineInitial ∧
      OrdinaryActualTraceTriangleFineCoverAtLocalBalance 2 ρ₀ pmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad κ β ηbal d mFineLater ∧
      ∀pH:ℝ,0≤pH→pH≤1→
        OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold 2 0 d k mGeom β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh pH r r
          βparent b B εparent gap βout ζout ηpack εout :=by
  obtain ⟨mInitial,mBalance,hmI,hmB,hInitial,hBalance⟩:=hcallbacks d β hβ hβ1 hβInitial hβDeep 0 (by norm_num)
  obtain ⟨mEdit,Nedit,hmEdit,hMargins⟩:=hmargins β hβ hβ1 hβEdit
  obtain ⟨mFine,mFineInitial,mFineLater,_,hFI,hFL,hFine,hLater⟩:=
    ordinary_triangle_initial_later_fine_cover_shared_choice d ρ₀ pmin href κ δcut ζcut εcut ζlimit εsample εvortex ε ξroot aLoad ηbal αcut pstar β
      hnum hρ₀ hε hεv hδ hδsmall hξ hξEq ha ha1 hbal.le hbalcap hβ hβ1 hζcut hεcut hζlimit hδlim hhref
  obtain ⟨mGeom,hmGeom,hGeom⟩:=ordinary_vortex_sharp_geometry_from_rates_uniform_spoke 2 0 d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh r r
    βparent b B εparent gap βout ζout ηpack εout hgeometry hβ hβ1 hε hεsmall hρ₀ hγ hlam hlam1 hlamρ hξreserve hεξ hερ hεroot
    hβe hβh hp hr hr hξ.le ha.le hbal.le hηI.le hedit hβcap hrcap hrcap hξcap haCap hbalCap hηIcap
    (by simpa using hrow) (by norm_num at hlevel ⊢; exact hlevel) haEdit hlamE hlamH
  let mAll:=max mInitial (max mBalance (max mEdit (max mFine mGeom)))
  have hI:mInitial≤mAll:=le_max_left _ _
  have hB:mBalance≤mAll:=(le_max_left _ _).trans (le_max_right _ _)
  have hE:mEdit≤mAll:=((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hF:mFine≤mAll:=(((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hG:mGeom≤mAll:=(((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  exact ⟨mInitial,mBalance,mEdit,Nedit,mFineInitial,mFineLater,mGeom,mAll,hmI,hmB,hmEdit,hmGeom,hI,hB,hE,hFI.trans hF,hFL.trans hF,hG,
    hInitial,hBalance,hMargins,hFine,hLater,hGeom⟩
end Oberwolfach
