module

public import Oberwolfach.OrdinaryTrackedHistoryFromSampleLevel
public import Oberwolfach.OrdinarySelectedParentCertificateParameters

@[expose] public section
/-! Assemble the later-history certificate uniformly at every level, using
one selected parent record and level-data packages from the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

theorem ordinary_tracked_later_callback_from_common_levels
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
    (weight:∀i,OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q i)) (mWheel+1)→ℝ):
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
    ∀i,i+1<Q.length→∀A (G:SimpleGraph (Fin n)) (Hs:Fin n→Fin q→Prop),
    OrdinaryUniformProtectedBalanceHistory Gstart Hstart
      (fun t=>Q.extendedVertices (t+1)) (fun t=>Q.extendedVertices (t+2))
      (fun t=>Q.extendedIndices (t+1)) (fun t=>Q.extendedIndices (t+2))
      (ordinaryVortexSelectedCost Q rate) (ordinaryFineDeepCost Q ξroot) (mWheel+1) (i+1) Q.length A
      (fun t=>Q.extendedVertices (t+2)) (fun t=>Q.extendedVertices (t+1)) (fun t=>Q.extendedIndices (t+2))
      (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
    ordinaryHostResources G Hs=A→G≤Gbase→(∀v u,Hs v u→Hbase v u)→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    let fv:=markedVortexVertexEmbedding Q (i+1);let gu:=markedVortexHubEmbedding Q (i+1);
    OrdinaryWheelLikelySeparateCostsCertificate (G.comap fv) (Bad.comap fv) (fun v u=>Hs (fv v) (gu u))
      (markedVortexInnerVertices Q (i+1)) (ordinaryVortexBufferedVertices Q (i+1) 2)
      (markedVortexInnerHubs Q (i+1)) (ordinaryVortexBufferedHubs Q (i+1) 2) (mWheel+1)
      (rate*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)))
      (10*ξroot*(markedVortexInnerVertices Q (i+1)).card) :=by
  intro raw Bad Reference Href Bweight cert Gbase Hbase Gstart Hstart hcert hw hf hsample hpack hbase hbudget
    i hi A G Hs hhist hstate hG hH hbal hdiv fv gu
  have hsize:=hlevelsize (i+1) hi
  have hρpos:0< initialIndexDensity (Fin q) D:=hρ.trans_le hρlo
  have hh:=ordinary_tracked_history_from_sample_level mWheel loadK d hmWheel ρ₀ pstar pstar href δcut ζcut εcut ζlimit εsample
    ε ξroot aLoad a ρdeep θdeep β ηbal ηProfile α ζ cBoundary δDeep rate 0 rateParent mBalance mCover mInitial ηInitial δInitial
    hrate le_rfl hInitialAt hbalance hcover hζlim hζrate hζcut hεcut hζlimit
    n q P Target G Hs D mv hreg hn hhalf hρlo hρhi hmB hmC Q π hπ σx coins sp Kres i hi
    Fs Comps embed mAbs tAbs aAbs bAbs Ares Wterm Bterm ξabs editCost JQ JH
    A pR pH θhost εR εH (eParent*ε) (hParentRate*ε) αcut pstar ηHub cHub Bweight capHub hζcap
    hpR hpR1 hpH hpH1 hθhost hdegree hpEq hsp hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβecap hβh0 hβhcap
    hw hf hstate Q.length (Nat.lt_trans (Nat.lt_succ_self i) hi) hρpos hβ0 hβ1 hε hmv hhist hmI hεRinitial hεHinitial hηInitial hbal hdiv hpHpos hcut hhref
    k hk βH ηH Bhost βparent εparent ζparent gapParent lamRoot hParent δparent cParent N₀
    hBhost hρ hpstar hζparent hN₀ hscale hroot hsize.1 βP ηP row εTri (weight (i+1)) hpR hpH hcParent
    eParent hParentRate CHub rfl rfl rfl rfl (hsample (i+1) hi) hξroot haLoad hηbal
    βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap mGeom hmGeo hlamRoot hgeometry
    Ncert N hNcert hNsize hterminal δend ζhub ζlocal γcert eParent hδend hRend hHend hRateEnd hRate0 hζhub hζlocal hγcert hγe hlam hlam1
    cert hcert rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hParentRate rfl rfl (by simp [cert,ordinarySelectedParentCertificateParameters])
    (by simp [cert,ordinarySelectedParentCertificateParameters]) hpack
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hκ) hpR hpH
    Nfinish M rate θmatch ellCap finishCap kcap hθmatch
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hθcap)
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hεsup)
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hpθ)
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hsqrt) hbase hsize.2
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hell) hcoverCap hbudget
    (by simpa [cert,ordinarySelectedParentCertificateParameters] using hsched)
  convert hh using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
end Oberwolfach
