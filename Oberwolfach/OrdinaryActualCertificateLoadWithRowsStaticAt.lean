module

public import Oberwolfach.OrdinaryActualCertificateLoadWithPlacementAt
public import Oberwolfach.OrdinaryParentEventsAtSpacing
public import Oberwolfach.OrdinaryOriginalPreSampleWithEditRatesAt
public import Oberwolfach.OrdinaryPreSampleForInitialPlacementBudget

@[expose] public section
/-! The exact local certificate load and the later matching placement share
one tolerance and one selected spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryActualCertificateLoadWithRowsStaticAt
    (mWheel loadK k:ℕ) (hm:3≤mWheel) (α βparent ω bRoot BRoot hpack δ εstar cLinear:ℝ)
    (ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γ bHub BHub p₀ κ ηhub ζhub ζlocal δend:ℝ)
    (eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate pcap:ℝ)
    (L rstar mEarly kEarly dMin:ℕ) (βfreq αOriginal γList capInner θhost capOriginal:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (βP ηP row ηH βH cParent BParent δref hrefParent:ℝ) (hp:0<pmin)
    (capHub αcorr pstar ωcorr δAbs hAbs εabs εv:ℝ):Prop :=
    ∃ellCap kcap pbound p εsup finishCap δsample loadCap ν cap:ℝ,
      ellCap=θmatch/64 ∧ 0<ellCap ∧ 0<kcap ∧ 0<pbound ∧ pbound≤pcap ∧
      0<p ∧ p≤pbound ∧ p≤1 ∧ p≤4*θmatch ∧ 20*Real.sqrt (2*p)≤θmatch/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<finishCap ∧ finishCap≤a ∧ finishCap≤ellCap ∧
      0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧ loadCap≤finishCap ∧ 0<ν ∧ 0<cap ∧ ν≤finishCap ∧ cap≤finishCap ∧
    ∃Nfinish:ℕ,
      (∀n:ℕ,Nfinish≤n→2≤θmatch*p*n/4 ∧
        ∃Kcap Dmax:ℕ,0<Kcap ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤kcap^2*n ∧
        ∀τ ηrate ellrate Lconf:ℝ,0≤τ→τ≤cap→0≤ηrate→ηrate≤finishCap→0≤ellrate→ellrate≤ellCap→
          Lconf≤kcap^2*n→
          (βe*n+3*max (ηrate*n) (ellrate*n)≤(eParent*ε)*n ∧
           βh*n+2*(ellrate*n)≤(hParent*ε)*n) ∧
          (τ+ν≤p^2/4 ∧ τ+ν+(p*ellrate+δsample)≤θmatch*p/4 ∧ ν+ηrate≤θmatch*p/4) ∧
          (((n*Dmax*(mWheel+1):ℕ):ℝ)/(Kcap:ℝ)+
            (((mWheel+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((Kcap+Dmax:ℕ):ℝ))+
            (Dmax:ℝ)+((Dmax*(mWheel+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*(ν*n) ∧
           ν*n+ηrate*n+2*((2*p)*n)+((3*(Kcap+Dmax)+Dmax*(mWheel+1):ℕ):ℝ)≤rate*n)) ∧
    ∃τ ηpack:ℝ,τ=ordinarySafeCleanupScale (mWheel+1) p βe (βh/2) ν (min cap 1) ∧
      0<τ ∧ τ≤cap ∧ τ≤1 ∧ 0<ηpack ∧ cLinear*τ≤ηpack ∧
    ∃n₀:ℕ,∃εout γgeom aLoad ξroot η₀ ηbal ηInitial βcap δcap δInitial δedit ηedit:ℝ,
      0<εout ∧ εout≤1 ∧ 0<γgeom ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤loadCap ∧ aLoad≤a ∧ aLoad≤γgeom/1000 ∧
      aLoad≤edit/(72*((mWheel:ℝ)+2)) ∧ ξroot=min (ε/200) (aLoad^2/160) ∧
      0<ξroot ∧ ξroot≤ε/100 ∧ ξroot≤γgeom/160000 ∧ 80*ξroot≤aLoad^2 ∧
      max (18*aLoad+3*(((loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((mWheel:ℝ)+1))≤ellCap ∧ 10*ξroot≤finishCap ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γgeom/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ 0<βcap ∧ βcap≤1/4 ∧ βcap≤γgeom/1000 ∧
      0<δcap ∧ δcap≤γgeom/1000 ∧ 0<δInitial ∧ δInitial≤α ∧ δInitial≤ηInitial ∧
      0<δedit ∧ δedit≤α ∧ δedit≤ηbal ∧ 0<ηedit ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (mWheel+1) k 2 ρ₀ βparent b B εparent gap
        βout ξreserve ζout edit p ηpack εout γgeom ∧
    ∃ηBudget capChosen:ℝ,0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζ*ε/2 ∧
      0<capChosen ∧ capChosen≤capOriginal ∧ capChosen≤ηBudget ∧
    ∃dSelected:ℕ,∃hdSelected:2≤dSelected,
      OrdinaryOriginalPreSampleWithEditRatesAt L rstar dSelected mEarly kEarly dMin βfreq ρ₀ αOriginal γList capInner capChosen θhost
        hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
        ε capHub ηBudget αcorr pstar ωcorr δAbs hAbs εabs εv ∧
      OrdinaryParentEventsAtSpacing mWheel k dSelected hm hdSelected α ρ₀ pmin
        βP ηP row ηH βH cParent BParent δref hrefParent ε hp ∧
    ∃εR εH:ℝ,0<εR ∧ 0<εH ∧ εR≤δcap ∧ εH≤δcap ∧
      εR≤δInitial ∧ εH≤δInitial ∧ εR≤εsample ∧ εH≤εsample ∧
      εR≤δDeep ∧ εH≤δDeep ∧ εR≤δend/4 ∧ εH≤δend/4 ∧
      εR≤δedit ∧ εH≤δedit ∧
    ∀(d:ℕ),∃Nclean Nreserve Ncert:ℕ,
      OrdinaryVortexFineCertificateAtGeneralLoad {m:=mWheel, k:=k, loadK:=loadK, hm:=hm, α:=α, ω:=ω, β:=βout, bRoot:=bRoot, BRoot:=BRoot, hpack:=hpack, δ:=δ, εstar:=εstar, ηpack:=ηpack, γ:=γ, bHub:=bHub, BHub:=BHub, p₀:=p₀, κ:=κ, ηhub:=ηhub, ζhub:=ζhub, ζlocal:=ζlocal, δend:=δend, b₀:=2*(3*d), p:=p, βe:=βe, βh:=βh, ν:=ν, cap:=cap, εsup:=εsup, δsample:=δsample, τ:=τ, L:=((2*(3*d):ℕ):ℝ), n₀:=n₀, Nclean:=Nclean, εgeom:=εout, Nreserve:=Nreserve, Ncert:=Ncert} ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∀C:ℝ,0≤C→
    ∃mInitial mBalance mCover mEdit Nedit:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧ 1≤mEdit ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε ηbal cInitial δedit ηedit β d mEdit Nedit ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover ∧
    ∀εR εH pH:ℝ,0≤εR→εR≤δcap→0≤εH→εH≤δcap→0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout
end Oberwolfach
