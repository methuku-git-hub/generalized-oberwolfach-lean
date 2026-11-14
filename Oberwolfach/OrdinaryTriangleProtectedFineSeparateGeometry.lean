module

public import Oberwolfach.OrdinaryTriangleParentToleranceAndDeepBalance
public import Oberwolfach.OrdinaryTriangleRootFreeRateFineBalanceChoiceWithCap
public import Oberwolfach.OrdinaryTriangleInnerSelectedNumericDomain

@[expose] public section
/-! Choose the protected cost rate before the fine-completion rate.  The
inner numerical domain supplies both parent-rate caps, and the fine load is
kept below the outer-hub cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_protected_fine_separate_geometry
    (α ρ₀ pmin cInner CInner ηhub eParent hParent κe ηend εf εrows othercap:ℝ)
    (ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold βcap:ℝ)
    (ε ηProfile cBoundary:ℝ)
    (hselected:OrdinaryTriangleInnerSelectedNumericDomain α cInner CInner ε ρ₀ pmin ηhub eParent hParent κe ηend εf εrows othercap
      ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold βcap)
    (hDeep:OrdinaryTriangleInitialDeepBalanceSelector ρ₀ α pmin pmin cBoundary) (hηProfile:0<ηProfile)
    (βH ηH Bparent ω βparent εparent ζparent rateRoot:ℝ) (N₀:ℕ)
    (hN₀:1≤N₀) (hroot:0<rateRoot)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH Bparent ω pmin βparent εparent ζparent rateRoot N₀)
    (ζlimit:ℝ) (hLimit:0<ζlimit)
    (k:ℕ) (βout b B hpack δref εstar cLinear ζfresh:ℝ)
    (βgeo εgeo gap ξreserve ζout edit γbase βe βh ellCap lam lamRoot δcut εcap θmatch κhub:ℝ)
    (hVortex:OrdinaryTriangleEarlyVortexData ρ₀ lamRoot ξreserve edit εcap ζfresh γbase lam ε βe βh θmatch ellCap)
    (hchoice:OrdinaryTriangleRootFreeRateActualAfterVortex α k ω βout b B hpack δref εstar cLinear κe pmin cInner (4*CInner/pmin^7)
      εf ηhub ηend ζfresh εrows ρ₀ βgeo εgeo gap ξreserve ζout edit eParent hParent γbase ε βe βh ellCap)
    (hρ₀:0<ρ₀) (hδcut:0<δcut) (hedit:0<edit) (hκhub:0<κhub):
    ∃rateParent ζcert δDeep rate:ℝ,
      0<rateParent ∧ rateParent≤rateRoot ∧ rateParent≤lamInner*ε/4 ∧ rateParent≤δInner*ε/8 ∧
      OrdinaryTriangleEditScaleAt βH ηH Bparent ω pmin βparent εparent ζparent rateParent N₀ ∧
      0<ζcert ∧ ζcert≤rateParent ∧ ζcert≤capInner ∧ ζcert≤ζlimit ∧
      0<δDeep ∧ δDeep≤α ∧ 0<rate ∧
    ∃p εsup capSmall δsample ν:ℝ,
      0<p ∧ p≤1 ∧ p≤4*ζfresh*(γbase*ε) ∧
      20*Real.sqrt (2*p)≤ζfresh*(γbase*ε)/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<capSmall ∧ capSmall≤κhub ∧ capSmall≤ellCap ∧
      0<δsample ∧ 0<ν ∧ ν≤capSmall ∧
    ∃Norder:ℕ,(∀n:ℕ,Norder≤n→2≤ζfresh*(γbase*ε)*p*n/4) ∧
    ∃τ:ℝ,τ=ordinarySafeCleanupScale 3 p βe (βh/2) ν (min capSmall 1) ∧
      0<τ ∧ τ≤capSmall ∧ τ≤1 ∧
      τ+ν≤p^2/4 ∧ τ+ν+(p*ellCap+δsample)≤ζfresh*(γbase*ε)*p/4 ∧
      ν+capSmall≤ζfresh*(γbase*ε)*p/4 ∧ ν+capSmall+4*p≤rate ∧
      βe+3*max capSmall ellCap≤eParent*ε ∧ βh+2*ellCap≤hParent*ε ∧
    ∃eps γgeo aLoad ξroot η₀ ηbal ηInitial:ℝ,
      0<eps ∧ eps≤1 ∧ 0<γgeo ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βgeo b B εgeo gap
        βout ξreserve ζout edit p (cLinear*τ) eps γgeo ∧
      OrdinaryTriangleRootFreeActualCoverAfterCleanup α k ω βout b B hpack δref εstar cLinear κe pmin cInner (4*CInner/pmin^7)
        εf ηhub ηend ζfresh εrows p βe βh ν capSmall εsup δsample τ ∧
      0<aLoad ∧ aLoad≤1 ∧ aLoad≤capSmall ∧ aLoad≤κhub ∧ aLoad≤γgeo/1000 ∧ aLoad≤edit/(72*((2:ℝ)+2)) ∧
      ξroot=min (ε/200) (aLoad^2/160) ∧ 0<ξroot ∧ ξroot≤γgeo/160000 ∧ 10*ξroot≤capSmall ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γgeo/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ ηbal+100*ξroot≤γgeo/8 ∧ ηInitial+100*ξroot≤γgeo/8 ∧
      max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap ∧
    ∃δInitial:ℝ,0<δInitial ∧ δInitial≤α ∧ δInitial≤ηInitial ∧
    ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
    ∃mInitial mBalance:ℕ,1≤mInitial ∧ 1≤mBalance ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin pmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin pmin ηProfile ζcert cBoundary δDeep rate d 2 β C mBalance :=by
  obtain ⟨hξ,hξη,hK,hB,ht,he,hh,hcap,heP,hhP,hKdom,hsetup,hdeep,hinner,hβcap,hother,hβ⟩:=hselected
  obtain ⟨hε,hεcap,hεsmall,hεξ,hερ,hlameq,hlam,hlamRoot,hlam1,hlamρ,hβe,hβh,hlamE,hlamH,hrow,hlevel,
    hθmatch,hEllEq,hEll,hrootEll,hEllUpper⟩:=hVortex
  obtain ⟨rateParent,ζcert,δDeep,rate,hrate,hrateRoot,hrateInner,hrateEnd,hscale',hζ,hζrate,hζcap,hζlimit,
    hδDeep,hδα,hrateDeep,hbalance⟩:=
    ordinary_triangle_parent_tolerance_and_deep_balance ρ₀ α pmin pmin cBoundary ηProfile hDeep hηProfile
      βH ηH Bparent ω pmin βparent εparent ζparent rateRoot lamInner δInner ε N₀
      hN₀ hroot hinner.lambda_pos hinner.delta_pos hε hεsmall hscale capInner ζlimit hcap hLimit
  obtain ⟨p,εsup,capSmall,δsample,ν,hp,hp1,hpCap,hpθ,hsqrt,hεsup,hεsupCap,hcapSmall,hcapOther,hcapEll,
    hδsample,hν,hνcap,Norder,hNorder,τ,hτeq,hτ,hτcap,hτ1,hsafe1,hsafe2,hsafe3,hfinish,hbudgetE,hbudgetH,
    eps,γgeo,aLoad,ξroot,η₀,ηbal,ηInitial,heps,heps1,hγ,hgeometry,hcover,ha,ha1,hacapSmall,haγ,haedit,hξeq,hξ,hξγ,hξcap,
    hηeq,hη₀,hη,hη₀cap,hηγ,hηI,hηIcap,hsmall,hsmall',hellBound⟩:=
    ordinary_triangle_root_free_rate_fine_balance_choice_with_cap α k ω βout b B hpack δref εstar cLinear κe pmin cInner (4*CInner/pmin^7)
      εf ηhub ηend ζfresh εrows ρ₀ βgeo εgeo gap ξreserve ζout edit eParent hParent γbase ε βe βh ellCap lam δcut
      hchoice hρ₀ hε hδcut hedit hlam.le hEll hrootEll rate 1 κhub hrateDeep (by norm_num) hκhub
  obtain ⟨δInitial,hδInitial,hδIα,hδIη,hcallbacks⟩:=hbalance ηInitial hηI
  exact ⟨rateParent,ζcert,δDeep,rate,hrate,hrateRoot,hrateInner,hrateEnd,hscale',hζ,hζrate,hζcap,hζlimit,
    hδDeep,hδα,hrateDeep,p,εsup,capSmall,δsample,ν,hp,hp1,hpθ,hsqrt,hεsup,hεsupCap,hcapSmall,hcapOther,hcapEll,
    hδsample,hν,hνcap,Norder,hNorder,τ,hτeq,hτ,hτcap,hτ1,hsafe1,hsafe2,hsafe3,hfinish,hbudgetE,hbudgetH,
    eps,γgeo,aLoad,ξroot,η₀,ηbal,ηInitial,heps,heps1,hγ,hgeometry,hcover,ha,ha1,hacapSmall,hacapSmall.trans hcapOther,haγ,haedit,hξeq,hξ,hξγ,hξcap,
    hηeq,hη₀,hη,hη₀cap,hηγ,hηI,hηIcap,hsmall,hsmall',hellBound,
    δInitial,hδInitial,hδIα,hδIη,hcallbacks⟩
end Oberwolfach
