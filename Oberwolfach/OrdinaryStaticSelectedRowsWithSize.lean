module

public import Oberwolfach.OrdinaryStaticCertificateFixedMatchingRows
public import Oberwolfach.OrdinarySelectedCertificateMatchingThreshold

@[expose] public section
/-! Add one common wheel and conflict size threshold without changing the
selected static geometry, matching or correction rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryStaticSelectedRowsWithSizeAt
    (mWheel loadK k:ℕ) (hm:3≤mWheel) (α βparent ω bRoot BRoot hpack δ εstar cLinear:ℝ)
    (ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γ bHub BHub p₀ κ ηhub ζhub ζlocal δend:ℝ)
    (eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate pcap:ℝ)
    (L rstar mEarly kEarly dMin:ℕ) (βfreq αOriginal γList capInner θhost capOriginal:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (capHub αcorr pstar ωcorr δAbs hAbs εabs εv:ℝ) (Nextra:ℕ):Prop :=
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
    ∃dSelected:ℕ,∃hdSelected:2≤dSelected,∃ξedit ξAbs:ℝ,
      ξedit≤capHub ∧ ξAbs≤capHub ∧
      OrdinaryOriginalPreSampleFixedJointRatesAt L rstar dSelected mEarly kEarly dMin βfreq ρ₀ αOriginal γList capInner capChosen θhost
        hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly ε capHub ηBudget αcorr pstar ωcorr δAbs hAbs εabs εv ξedit ξAbs ∧
      (∀(βv:ℝ) (mv:ℕ) (ζfail χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ),
        0<ζfail→0<χpair→0<χlist→0<χbal→0<χbd→0<χnbr→0<χpairR→0<χpath→
        0<χlocal→0<χglobal→0<χhub→0<χcol→
        OrdinaryOriginalPreSampleJointThresholdsSeparateListsAt L rstar dSelected mEarly kEarly dMin βfreq ρ₀ αOriginal γList capInner capChosen θhost
          hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly ε capHub ηBudget αcorr pstar ωcorr δAbs hAbs εabs εv
          mv (2*mv) 10 ζfail χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol ξedit ξAbs βv) ∧
    ∃rowTolerance:ℝ,0<rowTolerance ∧ rowTolerance≤δInitial ∧ rowTolerance≤δDeep ∧ rowTolerance≤δedit ∧
      rowTolerance≤εsample ∧ rowTolerance≤γgeom/1000 ∧ rowTolerance≤δend/4 ∧ rowTolerance≤δcap ∧
    ∀(d:ℕ),∃Nclean Nreserve Ncert:ℕ,
      OrdinaryVortexFineCertificateAtGeneralLoad {m:=mWheel, k:=k, loadK:=loadK, hm:=hm, α:=α, ω:=ω, β:=βout, bRoot:=bRoot, BRoot:=BRoot, hpack:=hpack, δ:=δ, εstar:=εstar, ηpack:=ηpack, γ:=γ, bHub:=bHub, BHub:=BHub, p₀:=p₀, κ:=κ, ηhub:=ηhub, ζhub:=ζhub, ζlocal:=ζlocal, δend:=δend, b₀:=2*(3*d), p:=p, βe:=βe, βh:=βh, ν:=ν, cap:=cap, εsup:=εsup, δsample:=δsample, τ:=τ, L:=((2*(3*d):ℕ):ℝ), n₀:=n₀, Nclean:=Nclean, εgeom:=εout, Nreserve:=Nreserve, Ncert:=Ncert} ∧
    let cert:OrdinaryVortexFineCertificateParametersGeneralLoad:={m:=mWheel, k:=k, loadK:=loadK, hm:=hm, α:=α, ω:=ω, β:=βout, bRoot:=bRoot, BRoot:=BRoot, hpack:=hpack, δ:=δ, εstar:=εstar, ηpack:=ηpack, γ:=γ, bHub:=bHub, BHub:=BHub, p₀:=p₀, κ:=κ, ηhub:=ηhub, ζhub:=ζhub, ζlocal:=ζlocal, δend:=δend, b₀:=2*(3*d), p:=p, βe:=βe, βh:=βh, ν:=ν, cap:=cap, εsup:=εsup, δsample:=δsample, τ:=τ, L:=((2*(3*d):ℕ):ℝ), n₀:=n₀, Nclean:=Nclean, εgeom:=εout, Nreserve:=Nreserve, Ncert:=Ncert};
    ∃M:ℕ,1≤M ∧ Nextra≤M ∧
      max (max (max (4*cert.n₀) (4*cert.Nreserve)) (max cert.Nclean 64)) (max cert.Ncert Nfinish)≤M ∧
      4/ε≤(M:ℝ) ∧ cert.L≤kcap^2*M ∧
      (∀n:ℕ,M≤n→∀cost:ℝ,cost≤14*ηBudget*n→cost+2*((3*d:ℕ):ℝ)≤15*ηBudget*n) ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∀C:ℝ,0≤C→
    ∃mInitial mBalance mCover mEdit Nedit:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧ 1≤mEdit ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε ηbal cInitial δedit ηedit β d mEdit Nedit ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover ∧
    ∀εR εH pH:ℝ,0≤εR→εR≤δcap→0≤εH→εH≤δcap→0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout

theorem ordinary_static_selected_rows_with_size
    (mWheel loadK k:ℕ) (hm:3≤mWheel) (α βparent ω bRoot BRoot hpack δ εstar cLinear:ℝ)
    (ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γ bHub BHub p₀ κ ηhub ζhub ζlocal δend:ℝ)
    (eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate pcap:ℝ)
    (L rstar mEarly kEarly dMin:ℕ) (βfreq αOriginal γList capInner θhost capOriginal:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (capHub αcorr pstar ωcorr δAbs hAbs εabs εv:ℝ) (Nextra:ℕ) (hε:0<ε) (h:OrdinaryStaticCertificateFixedMatchingRowsAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
      ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ bHub BHub p₀ κ ηhub ζhub ζlocal δend eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly capHub αcorr pstar ωcorr δAbs hAbs εabs εv):
    OrdinaryStaticSelectedRowsWithSizeAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
      ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ bHub BHub p₀ κ ηhub ζhub ζlocal δend eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly capHub αcorr pstar ωcorr δAbs hAbs εabs εv Nextra :=by
  obtain ⟨ellCap,kcap,pbound,p,εsup,finishCap,δsample,loadCap,ν,cap,hellEq,hell,hStaticChunksRest1⟩:=h
  obtain ⟨hkcap,hpbound,hpcap',hp,hpp,hp1,hpθ,hsqrt,hεsup,hεsupcap,hfinish,hfinishA,hStaticChunksRest2⟩:=hStaticChunksRest1
  obtain ⟨hfinishell,hδsample,hload,hload1,hloadfinish,hν,hcap,hνfinish,hcapfinish,Nfinish,hschedule,τ,hStaticChunksRest3⟩:=hStaticChunksRest2
  obtain ⟨ηpack,hτeq,hτ,hτcap,hτ1,hηpack,hlinear,n₀,εout,γgeom,aLoad,ξroot,hStaticChunksRest4⟩:=hStaticChunksRest3
  obtain ⟨η₀,ηbal,ηInitial,βcap,δcap,δInitial,δedit,ηedit,hεout,hεout1,hγgeom,haLoad,hStaticChunksRest5⟩:=hStaticChunksRest4
  obtain ⟨haLoad1,haLoadCap,haLoadA,haLoadγ,haLoadEdit,hξeq,hξ,hξε,hξγ,hξsq,hellRate,hcoverRate,hStaticChunksRest6⟩:=hStaticChunksRest5
  obtain ⟨hηeq,hη₀,hηbal,hηbal₀,hηbalγ,hηInitial,hηInitialBal,hβcap,hβcap1,hβcapγ,hδcap,hδcapγ,hStaticChunksRest7⟩:=hStaticChunksRest6
  obtain ⟨hδInitial,hδInitialα,hδInitialη,hδedit,hδeditα,hδeditη,hηedit,hstatic,ηBudget,capChosen,hBudget,hBudgetη,hStaticChunksRest8⟩:=hStaticChunksRest7
  obtain ⟨hsmall,hChosen,hOriginal,hCap,dSelected,hdSelected,ξedit,ξAbs,hξcap,hξAbscap,hjoint,hthresholds,hStaticChunksRest9⟩:=hStaticChunksRest8
  obtain ⟨rowTolerance,hrow,hrowInitial,hrowDeep,hrowEdit,hrowSample,hrowGeom,hrowEnd,hrowCap,hremain⟩:=hStaticChunksRest9
  refine ⟨ellCap,kcap,pbound,p,εsup,finishCap,δsample,loadCap,ν,cap,
    hellEq,hell,hkcap,hpbound,hpcap',hp,hpp,hp1,hpθ,hsqrt,hεsup,hεsupcap,hfinish,hfinishA,hfinishell,
    hδsample,hload,hload1,hloadfinish,hν,hcap,hνfinish,hcapfinish,
    Nfinish,hschedule,τ,ηpack,hτeq,hτ,hτcap,hτ1,hηpack,hlinear,
    n₀,εout,γgeom,aLoad,ξroot,η₀,ηbal,ηInitial,βcap,δcap,δInitial,δedit,ηedit,
    hεout,hεout1,hγgeom,haLoad,haLoad1,haLoadCap,haLoadA,haLoadγ,haLoadEdit,hξeq,hξ,hξε,hξγ,hξsq,
    hellRate,hcoverRate,hηeq,hη₀,hηbal,hηbal₀,hηbalγ,hηInitial,hηInitialBal,hβcap,hβcap1,hβcapγ,
    hδcap,hδcapγ,hδInitial,hδInitialα,hδInitialη,hδedit,hδeditα,hδeditη,hηedit,hstatic,
    ηBudget,capChosen,hBudget,hBudgetη,hsmall,hChosen,hOriginal,hCap,dSelected,hdSelected,ξedit,ξAbs,hξcap,hξAbscap,hjoint,hthresholds,
    rowTolerance,hrow,hrowInitial,hrowDeep,hrowEdit,hrowSample,hrowGeom,hrowEnd,hrowCap,?_⟩
  intro d
  obtain ⟨Nclean,Nreserve,Ncert,hcert,hsource⟩:=hremain d
  let cert:OrdinaryVortexFineCertificateParametersGeneralLoad:={m:=mWheel, k:=k, loadK:=loadK, hm:=hm, α:=α, ω:=ω, β:=βout, bRoot:=bRoot, BRoot:=BRoot, hpack:=hpack, δ:=δ, εstar:=εstar, ηpack:=ηpack, γ:=γ, bHub:=bHub, BHub:=BHub, p₀:=p₀, κ:=κ, ηhub:=ηhub, ζhub:=ζhub, ζlocal:=ζlocal, δend:=δend, b₀:=2*(3*d), p:=p, βe:=βe, βh:=βh, ν:=ν, cap:=cap, εsup:=εsup, δsample:=δsample, τ:=τ, L:=((2*(3*d):ℕ):ℝ), n₀:=n₀, Nclean:=Nclean, εgeom:=εout, Nreserve:=Nreserve, Ncert:=Ncert}
  obtain ⟨M,hM,hbase,hExtra,hfour,hbudget,hconf,_⟩:=
    ordinary_selected_certificate_matching_threshold cert ε ρ₀ kcap ηBudget d Nfinish Nextra hε hρ₀ hkcap hBudget
  exact ⟨Nclean,Nreserve,Ncert,hcert,M,hM,hExtra,hbase,hfour,hbudget,hconf,hsource⟩
end Oberwolfach
