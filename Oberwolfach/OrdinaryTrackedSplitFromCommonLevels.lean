module

public import Oberwolfach.OrdinaryTrackedLaterCallbackFromCommonLevels
public import Oberwolfach.OrdinaryTrackedInitialFromSampleLevel
public import Oberwolfach.OrdinaryTrackedSelectedCostSplitCertificates

@[expose] public section
/-! The actual initial and later wheel certificates use one selected parent
record, one corrected reservoir and one common expanded-sample outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

theorem ordinary_tracked_split_from_common_levels
    {n q mAbs tAbs aAbs bAbs:ℕ}
    (mWheel loadK d k:ℕ) (hmWheel:3≤mWheel) (hk:4≤k)
    (ρ₀ pstar href δcut ζcut εcut ζlimit εsample:ℝ)
    (ε ξroot aLoad a ρdeep θdeep β ηbal ηProfile α ζ cBoundary δDeep rate rateParent:ℝ)
    (mBalance mCover mInitial:ℕ) (ηInitial δInitial:ℝ)
    (hrate:0≤rate) (hInitialAt:OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pstar pstar ηInitial cBoundary δInitial d β mInitial)
    (hbalance:OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pstar pstar ηProfile ζ cBoundary δDeep rate d 2 β 0 mBalance)
    (hcover:OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ pstar href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρdeep θdeep β ηbal d mCover)
    (hζlim:ζ≤ζlimit) (hζrate:ζ≤rateParent) (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit)
    (P Target:SimpleGraph (Fin n)) (D mv:ℕ) (Q:Vortex (Fin q) P D β ε mv)
    (π:Equiv.Perm (Fin n)) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (σx:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (coins:Sym2 (Fin n)→Bool) (sp:Fin q→Bool→ℝ)
    (Fs:Fin q→SimpleGraph (Fin n)) (Comps:∀u,Finset (Fs u).ConnectedComponent)
    (embed:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉Comps u}↪Fin n)
    (Kres:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (Ares Wterm:Finset (Fin n)) (Bterm:Finset (Fin q))
    (ξabs editCost:ℝ) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (pR pH θhost εR εH αcut cHub CHub ηHub capHub eParent hParentRate:ℝ)
    (βP ηP row ηH βH cParent Bhost εTri βparent δparent hParent εparent gapParent ζparent lamRoot:ℝ) (N₀:ℕ)
    (βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap:ℝ) (mGeom:ℕ)
    (δend ζhub ζlocal γcert κ ν cap εsup δsample τ:ℝ)
    (n₀ Nclean Nreserve Ncert Nfinish M N:ℕ) (θmatch ellCap finishCap kcap:ℝ)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card (Fin n)) (hhalf:(Fintype.card (Fin n):ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity (Fin q) D) (hρhi:initialIndexDensity (Fin q) D≤1)
    (hmB:mBalance≤mv) (hmC:mCover≤mv) (hmI:mInitial≤mv) (hmGeo:mGeom≤mv)
    (hβ0:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hmv:0<mv)
    (hζcap:ζ≤capHub) (hpR:pstar≤pR) (hpR1:pR≤1) (hpH:pstar≤pH) (hpH1:pH≤1)
    (hθhost:1/2≤θhost) (hdegree:(θhost+α)*Fintype.card (Fin n)≤D)
    (hpEq:pR=initialIndexDensity (Fin q) D*pH) (hsp:∀u,sp u false=pH)
    (hεR0:0≤εR) (hεR:εR≤δDeep) (hεRsample:εR≤εsample)
    (hεH0:0≤εH) (hεH:εH≤δDeep) (hεHsample:εH≤εsample)
    (hβe0:0≤eParent*ε) (hβecap:eParent*ε≤cBoundary*ε)
    (hβh0:0≤hParentRate*ε) (hβhcap:hParentRate*ε≤cBoundary*ε)
    (hεRinitial:εR≤δInitial) (hεHinitial:εH≤δInitial) (hηInitial:ηInitial≤ηbal)
    (hpHpos:0<pH) (hcut:δcut≤min (αcut/32) (pstar/512)) (hhref:href≤αcut*pstar/64)
    (hBhost:0≤Bhost) (hpstar:0<pstar) (hζparent:0≤ζparent) (hN₀:1≤N₀)
    (hscale:OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH Bhost (ρ₀/16) pstar βparent εparent ζparent rateParent N₀)
    (hroot:OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad mWheel k loadK (Nat.le_trans (Nat.le_succ 2) hmWheel) α βparent cParent
      (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*hParent-ζparent) δparent εparent (ρ₀/16) gapParent lamRoot)
    (hξroot:0≤ξroot) (haLoad:0≤aLoad) (hηbal:0≤ηbal) (hcParent:0≤cParent)
    (hlam:0≤lamGeo) (hlam1:lamGeo≤1/4) (hlamRoot:lamGeo≤lamRoot)
    (hgeometry:OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold mWheel loadK d k mGeom β ε ρ₀ lamGeo ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βeGeo βhGeo pH εR εH
      (βparent/2) (cParent*(1-δparent)^mWheel) (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (εparent+gapParent) geomGap βout ζout ηpack εout)
    (hNcert:Ncert≤N) (hNsize:2/ε≤N) (hterminal:(N:ℝ)≤ε*mv/2)
    (hlevelsize:∀i,i<Q.length→N₀≤Fintype.card (markedVortexVertexType Q i) ∧ M≤(markedVortexInnerVertices Q i).card)
    (hδend:0≤δend) (hRend:εR≤δend/4) (hHend:εH≤δend/4) (hRateEnd:rateParent≤δend*ε/8) (hRate0:0≤rateParent)
    (hζhub:0<ζhub) (hζlocal:0<ζlocal) (hγcert:0<γcert) (hγe:γcert≤eParent)
    (hκ:κ≤ρ₀/8) (hθmatch:0<θmatch)
    (hθcap:θmatch≤(min (ζhub*γcert*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2)*ε)
    (hεsup:εsup≤p^2/4) (hpθ:p≤4*θmatch) (hsqrt:20*Real.sqrt (2*p)≤θmatch/2)
    (hell:max (18*aLoad+3*(((loadK:ℝ)+1)*lamGeo)) ((3*aLoad+lamGeo)*((mWheel:ℝ)+1))≤ellCap)
    (hcoverCap:10*ξroot≤finishCap)
    (hsched:OrdinaryAsymmetricFinishSchedule mWheel Nfinish eParent hParentRate ε βeGeo βhGeo θmatch p δsample ellCap finishCap kcap rate ν cap)
    (weight:∀i,OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q i)) (mWheel+1)→ℝ)
    (hFs:∀u,(Fs u).IsRegularOfDegree 2) (hsize:∀u (c:↥(Comps u)),Fintype.card c.val=mWheel+1)
    (hTarget:Target.IsRegularOfDegree (2*q)) (hTargetP:Target≤P)
    (mEdit Nedit mFine:ℕ) (ηedit ηBudget cInitial δedit:ℝ)
    (hNedit:Nedit≤n) (hmEdit:mEdit≤mv) (hmFine:mFine≤mv)
    (hMargins:OrdinaryInitialMatchingMarginsAt ρ₀ α pstar pstar ε ηbal cInitial δedit ηedit β d mEdit Nedit)
    (hFine:OrdinaryInitialFineCoverFromSharedAt mWheel loadK d ρ₀ pstar href a ρdeep θdeep δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar β mFine)
    (hεRedit:εR≤δedit) (hεHedit:εH≤δedit)
    (hβeInitial:eParent*ε≤cInitial*ε) (hβhInitial:hParentRate*ε≤cInitial*ε)
    (hβα:β≤2*α) (hηle:ηBudget≤ηedit) (hζ0:0≤ζ) (hsmall:15*ηBudget≤ζ*ε/2)
    (hcost0:0≤editCost) (hcost:editCost≤14*ηBudget*n) (hconf:editCost+2*((3*d:ℕ):ℝ)≤15*ηBudget*n)
    (hgeometryRoot:OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (mWheel+1) k 2 ρ₀ (βparent/2)
      (cParent*(1-δparent)^mWheel) (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (εparent+gapParent) geomGap
      βout ξreserve ζout edit p ηpack εout γgeom)
    (hγgeom:0<γgeom) (hlamρ:lamGeo≤(ρ₀/8)/2) (hξreserve:0≤ξreserve)
    (hεξ:ε≤ξreserve/2) (hερ:ε≤ξreserve*(ρ₀/8)/2) (hεroot:2*ε^2≤lamGeo)
    (hβeGeo:0≤βeGeo) (hβhGeo:0≤βhGeo) (hedit:0<edit)
    (hβcap:β≤γgeom/1000) (hRcap:εR≤γgeom/1000) (hHcap:εH≤γgeom/1000)
    (hξcap:ξroot≤γgeom/160000) (haCap:aLoad≤γgeom/1000) (hbalCap:ηbal≤γgeom/1000)
    (hrowCap:3*(((loadK:ℝ)+1)*lamGeo)≤edit/4) (hlevel:lamGeo*((mWheel:ℝ)+1)≤edit/4)
    (haEdit:aLoad≤edit/(72*((mWheel:ℝ)+2))) (hlamE:lamGeo≤βeGeo/4) (hlamH:lamGeo≤βhGeo/2):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σx e)
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P raw\Bad
    let Href:=rawWheelSpokes π d raw false
    let Bweight:=4*CHub/pstar^(3*mWheel+1)
    let cert:=ordinarySelectedParentCertificateParameters mWheel loadK k d n₀ Nclean Nreserve Ncert hmWheel
      α ρ₀ pstar βout cParent Bhost hParent δparent εparent gapParent geomGap
      ηpack γcert cHub Bweight pstar κ ηHub ζhub ζlocal δend p βeGeo βhGeo ν cap εsup δsample τ εout
    let Gbase:=Target\ordinaryEmbeddedComplements Fs Comps embed
    let Hbase:=fun v u=>v∉Set.range (embed u)
    let Gstart:=Gbase\ordinaryResourceRim Gbase Kres
    let Hstart:=fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈Kres);
    OrdinaryVortexFineCertificateAtGeneralLoad cert→
    OrdinaryCorrectedProtectedReservoirWitness (mWheel+1) mAbs tAbs aAbs bAbs ξabs Reference Bad Href
      Ares (Q.extendedVertices 1) Wterm Bterm (Q.extendedIndices 1) Kres JQ JH→
    OrdinaryTrackedComplementFor P Target π d σx Fs Comps (Q.extendedVertices 1) (Q.extendedIndices 1) Kres editCost embed→
    (∀i,i<Q.length→OrdinaryWheelSelectedSampleLevelData n q D mv mWheel loadK k d hmWheel β ε P Q π hπ
      α ρ₀ pstar βP ηP row ηH βH cParent Bhost εTri δparent hParent pR pH pstar αcut cHub CHub ηHub
      a aLoad ρdeep θdeep capHub eParent hParentRate εR εH
      (fun _=>θhost+α-β/2) (fun t=>εR*(markedVortexInnerVertices Q t).card)
      (fun t=>εH*(markedVortexInnerHubs Q t).card) sp false raw coins i (weight i))→
    cert.hpack≤(2*hParent-ζparent)-ξreserve-ζout→
    max (max (max (4*cert.n₀) (4*cert.Nreserve)) (max cert.Nclean 64)) (max cert.Ncert Nfinish)≤M→
    cert.L≤kcap^2*M→
    OrdinaryTrackedSplitWheelCertificatesAt P Target Bad Fs Comps (mWheel+1) Kres D mv β ε Q Q.length
      (ordinaryVortexSelectedCost Q rate) (ordinaryFineDeepCost Q ξroot) embed :=by
  intro raw Bad Reference Href Bweight cert Gbase Hbase Gstart Hstart hcert hw hf hsample hpack hbase hbudget
  have hLater:=ordinary_tracked_later_callback_from_common_levels (mAbs:=mAbs) (tAbs:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
    mWheel loadK d k hmWheel hk ρ₀ pstar href δcut ζcut εcut ζlimit εsample
    ε ξroot aLoad a ρdeep θdeep β ηbal ηProfile α ζ cBoundary δDeep rate rateParent mBalance mCover mInitial ηInitial δInitial
    hrate hInitialAt hbalance hcover hζlim hζrate hζcut hεcut hζlimit
    P Target D mv Q π hπ σx coins sp Fs Comps embed Kres Ares Wterm Bterm ξabs editCost JQ JH
    pR pH θhost εR εH αcut cHub CHub ηHub capHub eParent hParentRate
    βP ηP row ηH βH cParent Bhost εTri βparent δparent hParent εparent gapParent ζparent lamRoot N₀
    βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap mGeom
    δend ζhub ζlocal γcert κ ν cap εsup δsample τ n₀ Nclean Nreserve Ncert Nfinish M N θmatch ellCap finishCap kcap
    hreg hn hhalf hρ hρlo hρhi hmB hmC hmI hmGeo hβ0 hβ1 hε hmv hζcap hpR hpR1 hpH hpH1 hθhost hdegree hpEq hsp
    hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβecap hβh0 hβhcap hεRinitial hεHinitial hηInitial hpHpos hcut hhref
    hBhost hpstar hζparent hN₀ hscale hroot hξroot haLoad hηbal hcParent hlam hlam1 hlamRoot hgeometry
    hNcert hNsize hterminal hlevelsize hδend hRend hHend hRateEnd hRate0 hζhub hζlocal hγcert hγe hκ hθmatch hθcap hεsup hpθ hsqrt hell hcoverCap hsched weight
    hcert hw hf hsample hpack hbase hbudget
  have hzero:=hlevelsize 0 Q.length_pos
  have hn':0<n:=by simpa using hn
  have hhalf':(n:ℝ)/2≤D:=by simpa using hhalf
  have hdegree':(θhost+α)*(n:ℝ)≤D:=by simpa using hdegree
  have hinit:=ordinary_tracked_initial_from_sample_level (mAbs:=mAbs) (t:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
    P Target π d σx Fs hFs Comps hsize hTarget hTargetP
    (Q.extendedVertices 1) (Q.extendedVertices 1) Wterm Ares (Q.extendedIndices 1) (Q.extendedIndices 1) Bterm
    ξabs Kres JQ JH editCost embed D mv mEdit Nedit β ε θhost α ρ₀ pstar pstar ηbal cInitial δedit ηedit ηBudget ζ capHub
    Q hπ hn' hNedit hmEdit hmv hε hreg hhalf' hρ hρlo hρhi hβ0 hβα hθhost hdegree' hηle hζ0 hζcap hsmall hcost0 hcost hconf hMargins
    pR pH εR εH (eParent*ε) (hParentRate*ε) cHub Bweight ηHub sp hpR hpR1 hpH
    (hpstar.trans_le hpR).le (hpstar.trans_le hpH).le hεR0 hεRedit hεH0 hεHedit hβe0 hβeInitial hβh0 hβhInitial hpEq hsp
    loadK mFine href a ρdeep θdeep δcut ζcut εcut ζlimit εsample ξroot aLoad αcut pstar hFine hmFine hβ1 hpH1 hpHpos hεRsample hεHsample hζlim coins
    k N₀ Ncert N hmWheel hk βH ηH Bhost βparent εparent ζparent rateParent cParent hParent δparent gapParent lamRoot
    hBhost hpstar hζparent hN₀ hscale hroot βP ηP row εTri (weight 0)
    lamGeo γgeom edit βeGeo βhGeo βout ξreserve ζout p ηpack εout geomGap δend ζhub ζlocal γcert eParent
    cert hcert rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hParentRate rfl rfl (by simp [cert,ordinarySelectedParentCertificateParameters])
    (by simp [cert,ordinarySelectedParentCertificateParameters]) hpack
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hκ) hpR hpH
    Nfinish M rate θmatch ellCap finishCap kcap hθmatch
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hθcap)
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hεsup)
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hpθ)
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hsqrt) hbase hzero.2
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hell) hcoverCap hbudget
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hsched) CHub rfl rfl
    hw hf (hsample 0 Q.length_pos) hηbal hzero.1 hζrate hRate0 hpR hpH hcParent hgeometryRoot
    hγgeom hlam hlamRoot hlam1 hlamρ hξreserve hεξ hερ hεroot hβeGeo hβhGeo hξroot haLoad hedit
    hβcap hRcap hHcap hξcap haCap hbalCap hrowCap hlevel haEdit hlamE hlamH hNcert hNsize hterminal hδend hRend hHend hRateEnd hζhub hζlocal hγcert hγe
  exact ordinary_tracked_selected_cost_split_certificates P Target Bad Fs Comps (mWheel+1) Kres D mv β ε Q Q.length rate ξroot embed
    (by dsimp only [Bad]; convert hinit using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by
      intro i hi A G Hs hh hstate hG hH hbal hdiv
      have hout:=hLater i hi A G Hs
        (by convert hh using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
        (by convert hstate using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
        (by convert hG using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
        (by convert hH using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
        (by convert hbal using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
        (by convert hdiv using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
      dsimp only [Bad]
      convert hout using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
end Oberwolfach
