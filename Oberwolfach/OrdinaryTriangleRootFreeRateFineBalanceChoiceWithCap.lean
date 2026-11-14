module

public import Oberwolfach.OrdinaryTriangleRootFreeCoherentActualCoverChoices
public import Oberwolfach.OrdinaryTriangleFixedEllFineBalanceChoicesWithCap

@[expose] public section
/-! Once the protected cost rate is known, choose the root-free completion
and then its compatible fine-cover and balance rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_root_free_rate_fine_balance_choice_with_cap
    (α:ℝ) (k:ℕ) (ω βout b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (ρ₀ βparent εparent gap ξreserve ζout edit eParent hParent γbase ε βe βh ellCap lam δcut:ℝ)
    (hchoice:OrdinaryTriangleRootFreeRateActualAfterVortex α k ω βout b B hpack δref εstar cLinear κe pmin bHub BHub
      εf ηhub ηend ζfresh εrows ρ₀ βparent εparent gap ξreserve ζout edit eParent hParent γbase ε βe βh ellCap)
    (hρ₀:0<ρ₀) (hε:0<ε) (hδcut:0<δcut) (hedit:0<edit) (hlam:0≤lam) (hell:0<ellCap) (hroot:400*lam≤ellCap)
    (rate pcap othercap:ℝ) (hrate:0<rate) (hpcap:0<pcap) (hother:0<othercap):
    ∃p εsup capSmall δsample ν:ℝ,
      0<p ∧ p≤1 ∧ p≤pcap ∧ p≤4*ζfresh*(γbase*ε) ∧
      20*Real.sqrt (2*p)≤ζfresh*(γbase*ε)/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<capSmall ∧ capSmall≤othercap ∧ capSmall≤ellCap ∧
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
      OrdinaryTriangleRootFreeActualCoverAfterCleanup α k ω βout b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
        p βe βh ν capSmall εsup δsample τ ∧
      0<aLoad ∧ aLoad≤1 ∧ aLoad≤capSmall ∧ aLoad≤γgeo/1000 ∧ aLoad≤edit/(72*((2:ℝ)+2)) ∧
      ξroot=min (ε/200) (aLoad^2/160) ∧ 0<ξroot ∧ ξroot≤γgeo/160000 ∧ 10*ξroot≤capSmall ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γgeo/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ ηbal+100*ξroot≤γgeo/8 ∧ ηInitial+100*ξroot≤γgeo/8 ∧
      max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap :=by
  obtain ⟨p,εsup,capSmall,δsample,ν,hp,hp1,hpcap',hpθ,hsqrt,hεsup,hεsupCap,hcap,hcapOther,hcapEll,
    hδsample,hν,hνcap,Norder,hNorder,τ,hτeq,hτ,hτcap,hτ1,hsafe1,hsafe2,hsafe3,hfinish,hbudgetE,hbudgetH,
    eps,γgeo,heps,heps1,hγ,hgeometry,hcover⟩:=hchoice rate pcap othercap hrate hpcap hother
  obtain ⟨aLoad,ξroot,η₀,ηbal,ηInitial,ha,ha1,hacapSmall,haγ,haedit,hξeq,hξ,hξγ,hξcap,hηeq,hη₀,
    hη,hη₀cap,hηγ,hηI,hηIcap,hsmall,hsmall',hellBound⟩:=
    ordinary_triangle_fixed_ell_fine_balance_choices_with_cap ε δcut ρ₀ γgeo edit lam ellCap capSmall
      hε hδcut hρ₀ hγ hedit hlam hell hcap hroot
  exact ⟨p,εsup,capSmall,δsample,ν,hp,hp1,hpcap',hpθ,hsqrt,hεsup,hεsupCap,hcap,hcapOther,hcapEll,
    hδsample,hν,hνcap,Norder,hNorder,τ,hτeq,hτ,hτcap,hτ1,hsafe1,hsafe2,hsafe3,hfinish,hbudgetE,hbudgetH,
    eps,γgeo,aLoad,ξroot,η₀,ηbal,ηInitial,heps,heps1,hγ,hgeometry,hcover,ha,ha1,hacapSmall,haγ,haedit,hξeq,hξ,hξγ,hξcap,
    hηeq,hη₀,hη,hη₀cap,hηγ,hηI,hηIcap,hsmall,hsmall',hellBound⟩
end Oberwolfach
