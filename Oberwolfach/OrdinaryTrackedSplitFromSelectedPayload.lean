module

public import Oberwolfach.OrdinaryTrackedSplitFromCommonLevels
public import Oberwolfach.OrdinaryGeometryFinePayloadInputs

@[expose] public section
/-! The selected vortex payload supplies the shared initial and later
thresholds for the split wheel certificates on one sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

theorem ordinary_tracked_split_from_selected_payload
    {n q mAbs tAbs aAbs bAbs:ℕ}
    (mWheel loadK d k:ℕ) (hmWheel:3≤mWheel) (hk:4≤k)
    (ρ₀ pstar href δcut ζcut εcut ζlimit εsample:ℝ)
    (ε ξroot aLoad a ρdeep θdeep β ηbal ηProfile α ζ cBoundary δDeep rate rateParent:ℝ)
    (ηInitial δInitial:ℝ)
    (hrate:0≤rate)
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
    (βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap:ℝ)
    (δend ζhub ζlocal γcert κ ν cap εsup δsample τ:ℝ)
    (n₀ Nclean Nreserve Ncert Nfinish M N:ℕ) (θmatch ellCap finishCap kcap:ℝ)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card (Fin n)) (hhalf:(Fintype.card (Fin n):ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity (Fin q) D) (hρhi:initialIndexDensity (Fin q) D≤1)
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
    (ηedit ηBudget cInitial δedit:ℝ)
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
    (haEdit:aLoad≤edit/(72*((mWheel:ℝ)+2))) (hlamE:lamGeo≤βeGeo/4) (hlamH:lamGeo≤βhGeo/2)
    (m₀ Nmin Nextra:ℕ) (hm₀:m₀≤mv) (hNmin:Nmin≤n)
    (hpayload:OrdinaryVortexGeometryCostPayload mWheel loadK d k ε ρ₀ lamGeo ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βeGeo βhGeo εR εH
      (βparent/2) (cParent*(1-δparent)^mWheel) (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (εparent+gapParent) geomGap βout ζout ηpack εout capHub rate β
      (fun β' m' N'=>∃mLocal mFine:ℕ,mLocal≤m' ∧ mFine≤m' ∧
        (Nextra≤N' ∧ OrdinaryDeepLocalCertificateThresholdPayload mWheel loadK d
          ρ₀ α pstar pstar href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρdeep θdeep
          ηbal cBoundary cInitial δInitial ηInitial ηProfile ζ δDeep rate 0 δedit ηedit β' mLocal N') ∧
        OrdinaryInitialFineCoverFromSharedAt mWheel loadK d ρ₀ pstar href a ρdeep θdeep δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar β' mFine)
      m₀ Nmin):
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
  obtain ⟨mGeom,mCost,mFine,mInitial,mBalance,mCover,mEdit,Nedit,hmGeo,hmCost,hmFine,hmI,hmB,hmC,hmEdit,hExtra,hEditN,
    hMargins,hInitialAt,hbalance,hcover,hFine,hGeomAll,hSelectedCost⟩:=
    ordinary_geometry_fine_payload_inputs mWheel loadK d k m₀ Nmin Nextra mv
      ε ρ₀ lamGeo ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βeGeo βhGeo εR εH
      (βparent/2) (cParent*(1-δparent)^mWheel) (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (εparent+gapParent) geomGap βout ζout ηpack εout capHub rate β
      α pstar pstar href δcut ζcut εcut ζlimit εsample a ρdeep θdeep cBoundary cInitial δInitial ηProfile ζ δDeep δedit ηedit αcut pstar hpayload hm₀
  have hNedit:Nedit≤n:=hEditN.trans hNmin
  have hpH0:0≤pH:=(hpstar.trans_le hpH).le
  have hgeometry:=hGeomAll pH hpH0 hpH1
  exact ordinary_tracked_split_from_common_levels (mAbs:=mAbs) (tAbs:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
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
    hFs hsize hTarget hTargetP mEdit Nedit mFine ηedit ηBudget cInitial δedit hNedit hmEdit hmFine hMargins hFine
    hεRedit hεHedit hβeInitial hβhInitial hβα hηle hζ0 hsmall hcost0 hcost hconf hgeometryRoot
    hγgeom hlamρ hξreserve hεξ hερ hεroot hβeGeo hβhGeo hedit hβcap hRcap hHcap hξcap haCap hbalCap hrowCap hlevel haEdit hlamE hlamH
    hcert hw hf hsample hpack hbase hbudget
end Oberwolfach
