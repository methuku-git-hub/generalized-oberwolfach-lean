module

public import Oberwolfach.OrdinaryTriangleProtectedFineFromSelectedDomain
public import Oberwolfach.OrdinaryTriangleMatchingSpacingAndJointRates

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

theorem ordinary_triangle_protected_fine_matching_choice
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
    (gap ξreserve ζout edit γbase βe βh ellCap lam lamRoot δcut εcap θmatch κhub:ℝ)
    (hVortex:OrdinaryTriangleEarlyVortexData ρ₀ lamRoot ξreserve edit εcap ζfresh γbase lam ε βe βh θmatch ellCap)
    (hchoice:OrdinaryTriangleRootFreeRateActualAfterVortex α k ω βout b B hpack δref εstar cLinear κe pmin cInner (4*CInner/pmin^7)
      εf ηhub ηend ζfresh εrows ρ₀ βparent εparent gap ξreserve ζout edit eParent hParent γbase ε βe βh ellCap)
    (hρ₀:0<ρ₀) (hδcut:0<δcut) (hedit:0<edit) (hκhub:0<κhub)
    (hα:0<α) (hpmin:0<pmin) (hεcapκ:εcap≤κhub) (hεcapρ:εcap≤ρ₀/16)
    (cOuter COuter cInitial:ℝ) (hcOuter:0<cOuter) (hCOuter:0<COuter)
    (htri:OrdinaryTriangleHubEarlyBeforeFailure α ρ₀ pmin κhub cOuter COuter)
    (hInitial:OrdinaryTriangleInitialMatchingMarginSelector ρ₀ α pmin pmin cInitial)
    (L m kMatch dMin:ℕ) (βfreq αOriginal γList capPlace θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L 3 d m kMatch dMin βfreq ρ₀ αOriginal γList capPlace capEdit θhost
        (by omega) hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly)
    (δAbs hAbs εabs εv:ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly 3 α pmin (ρ₀/4) δAbs hAbs εabs εv):
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
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap
        βout ξreserve ζout edit p (cLinear*τ) eps γgeo ∧
      OrdinaryTriangleRootFreeActualCoverAfterCleanup α k ω βout b B hpack δref εstar cLinear κe pmin cInner (4*CInner/pmin^7)
        εf ηhub ηend ζfresh εrows p βe βh ν capSmall εsup δsample τ ∧
      0<aLoad ∧ aLoad≤1 ∧ aLoad≤capSmall ∧ aLoad≤κhub ∧ aLoad≤γgeo/1000 ∧ aLoad≤edit/(72*((2:ℝ)+2)) ∧
      ξroot=min (ε/200) (aLoad^2/160) ∧ 0<ξroot ∧ ξroot≤γgeo/160000 ∧ 10*ξroot≤capSmall ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γgeo/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ ηbal+100*ξroot≤γgeo/8 ∧ ηInitial+100*ξroot≤γgeo/8 ∧
      max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap ∧
    ∃δInitial:ℝ,0<δInitial ∧ δInitial≤α ∧ δInitial≤ηInitial ∧
    (∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
    ∃mInitial mBalance:ℕ,1≤mInitial ∧ 1≤mBalance ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin pmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin pmin ηProfile ζcert cBoundary δDeep rate d 2 β C mBalance) ∧
    ∃δedit ηedit ηBudget capChosen:ℝ,0<δedit ∧ δedit≤α ∧ δedit≤ηbal ∧ 0<ηedit ∧
      0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζcert*ε/2 ∧
      0<capChosen ∧ capChosen≤(1:ℝ) ∧ capChosen≤ηBudget ∧
    ∃d:ℕ,∃hd:2≤d,
      (∀β:ℝ,0≤β→β≤1/4→β≤δedit→∃m₀ N:ℕ,1≤m₀ ∧
        OrdinaryInitialMatchingMarginsAt ρ₀ α pmin pmin ε ηbal cInitial δedit ηedit β d m₀ N) ∧
    ∃bHub Bweight ξdeep t ζ δOuter δcap rateOuter ξedit ξAbs:ℝ,
      0<bHub ∧ bHub≤cOuter ∧ 0<Bweight ∧ (4*COuter/pmin^(3*2+1))*Kdom^2≤Bweight ∧
      0<ξdeep ∧ ξdeep≤(1:ℝ) ∧
      (∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤κhub ∧ β≤(1:ℝ) ∧ β≤betaCap ∧ ξdeep+2*β<ηhub) ∧
      0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δOuter ∧ δOuter≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rateOuter ∧
      OrdinaryVortexBufferedTraceCapCostWitness ε ρ₀ α pmin pmin ηbal ζ δOuter δcap rateOuter d 2 ∧
      OrdinaryTriangleHubAfterCapBeforeFailure d hd α ρ₀ pmin κhub aLoad ε ξdeep bHub Bweight ηhub δOuter δcap ∧
      OrdinaryOriginalPreSampleFixedJointRatesAt L 3 d m kMatch dMin βfreq ρ₀ αOriginal γList capPlace capChosen θhost
        (by omega) hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly ε δcap ηBudget α pmin (ρ₀/4) δAbs hAbs εabs εv ξedit ξAbs :=by
  obtain ⟨rateParent,ζcert,δDeep,rate,hrate,hrateRoot,hrateInner,hrateEnd,hscale',hζ,hζrate,hζcap,hζlimit,
    hδDeep,hδα,hrateDeep,p,εsup,capSmall,δsample,ν,hp,hp1,hpθ,hsqrt,hεsup,hεsupCap,hcapSmall,hcapOther,hcapEll,
    hδsample,hν,hνcap,Norder,hNorder,τ,hτeq,hτ,hτcap,hτ1,hsafe1,hsafe2,hsafe3,hfinish,hbudgetE,hbudgetH,
    eps,γgeo,aLoad,ξroot,η₀,ηbal,ηInitial,heps,heps1,hγ,hgeometry,hcover,ha,ha1,hacapSmall,haκ,haγ,haedit,hξeq,hξ,hξγ,hξcap,
    hηeq,hη₀,hη,hη₀cap,hηγ,hηI,hηIcap,hsmall,hsmall',hellBound,δInitial,hδInitial,hδIα,hδIη,hcallbacks⟩:=
    ordinary_triangle_protected_fine_from_selected_domain α ρ₀ pmin cInner CInner ηhub eParent hParent κe ηend εf εrows othercap
      ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold βcap ε ηProfile cBoundary
      hselected hDeep hηProfile βH ηH Bparent ω βparent εparent ζparent rateRoot N₀ hN₀ hroot hscale ζlimit hLimit
      k βout b B hpack δref εstar cLinear ζfresh gap ξreserve ζout edit γbase βe βh ellCap lam lamRoot δcut εcap θmatch κhub
      hVortex hchoice hρ₀ hδcut hedit hκhub
  have hε:0<ε:=hVortex.1
  have hεcap:ε≤εcap:=hVortex.2.1
  have hεsmall:ε<1/4:=hVortex.2.2.1
  have hηhub:0<ηhub:=by
    obtain ⟨hξ,hξη,_⟩:=hselected
    linarith
  have hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom:=by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hKdom,_⟩:=hselected
    exact hKdom
  refine ⟨rateParent,ζcert,δDeep,rate,hrate,hrateRoot,hrateInner,hrateEnd,hscale',hζ,hζrate,hζcap,hζlimit,
    hδDeep,hδα,hrateDeep,p,εsup,capSmall,δsample,ν,hp,hp1,hpθ,hsqrt,hεsup,hεsupCap,hcapSmall,hcapOther,hcapEll,
    hδsample,hν,hνcap,Norder,hNorder,τ,hτeq,hτ,hτcap,hτ1,hsafe1,hsafe2,hsafe3,hfinish,hbudgetE,hbudgetH,
    eps,γgeo,aLoad,ξroot,η₀,ηbal,ηInitial,heps,heps1,hγ,hgeometry,hcover,ha,ha1,hacapSmall,haκ,haγ,haedit,hξeq,hξ,hξγ,hξcap,
    hηeq,hη₀,hη,hη₀cap,hηγ,hηI,hηIcap,hsmall,hsmall',hellBound,δInitial,hδInitial,hδIα,hδIη,hcallbacks,?_⟩
  exact ordinary_triangle_matching_spacing_and_joint_rates L m kMatch dMin βfreq ρ₀ αOriginal γList capPlace θhost
    hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly hTail
    α pmin κhub cOuter COuter cInitial hInitial htri aLoad ε ηbal ζcert 1 ha haκ
    hε hεsmall (hεcap.trans hεcapκ) (hεcap.trans hεcapρ) hη hζ (by norm_num)
    1 ηhub Kdom ζlimit hα hκhub (by norm_num) hηhub hLimit hcOuter hCOuter hpmin hKdom 2 (by omega)
    α pmin (ρ₀/4) δAbs hAbs εabs εv hcorr
end Oberwolfach
