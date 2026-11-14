module

public import Oberwolfach.OrdinarySelectedParentCertificateBounds
public import Oberwolfach.OrdinaryTriangleAllLevelSizeFromTerminal
public import Oberwolfach.OrdinaryAssignedWheelSampleInputs
public import Oberwolfach.OrdinaryCommonEventUniformSplitFromPayload
public import Oberwolfach.OrdinaryWheelSelectedSampleLevelFromCommon
public import Oberwolfach.OrdinaryGeneralUniformMatchedWheelOutcome

@[expose] public section
/-! The actual parent/deep common event supplies its correction prior and
all selected wheel levels on the same sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_parent_assigned_ready_pointwise_outcome
    {n q mAbs tAbs aAbs bAbs:ℕ}
    (mWheel loadK d k:ℕ) (hmWheel:3≤mWheel) (hd:2≤d) (hk:4≤k)
    (ρ₀ pstar href δcut ζcut εcut ζlimit εsample:ℝ)
    (ε ξroot aLoad a ρdeep θdeep β ηbal ηProfile α ζ cBoundary δDeep rate rateParent:ℝ)
    (ηInitial δInitial:ℝ)
    (hrate:0≤rate)
    (hζlim:ζ≤ζlimit) (hζrate:ζ≤rateParent) (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit)
    (P:SimpleGraph (Fin n)) (D mv:ℕ) (Q:Vortex (Fin q) P D β ε mv)
    (π:Equiv.Perm (Fin n)) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (sp:Fin q→Bool→ℝ)
    (Rextra:(∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (Rextra σ)] (μ:FiniteLaw (∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e))
    (νextra:∀σ,FiniteLaw (Rextra σ))
    (Prior Extra:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e,Rextra σ)×(Sym2 (Fin n)→Bool)→Prop)
    (Fs:Fin q→SimpleGraph (Fin n)) (Comps:∀u,Finset (Fs u).ConnectedComponent)
    (Ares Wterm:Finset (Fin n)) (Bterm:Finset (Fin q)) (ξabs:ℝ)
    (Cost:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))→ℝ)
    (pRaw pH θhost εR εH αcut cHub CHub ηHub capHub eParent hParentRate:ℝ)
    (βP ηP row ηH βH cParent Bhost εTri βparent δparent hParent εparent gapParent ζparent lamRoot:ℝ) (N₀:ℕ)
    (βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap:ℝ)
    (δend ζhub ζlocal γcert κ ν cap εsup δsample τ:ℝ)
    (n₀ Nclean Nreserve Ncert Nfinish M N:ℕ) (θmatch ellCap finishCap kcap geomCap cMatch:ℝ)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card (Fin n)) (hhalf:(Fintype.card (Fin n):ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity (Fin q) D) (hρhi:initialIndexDensity (Fin q) D≤1)
    (hβ0:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hmv:0<mv)
    (hζcap:ζ≤capHub)
    (hθhost:1/2≤θhost) (hdegree:(θhost+α)*Fintype.card (Fin n)≤D)
    (hεR0:0≤εR) (hεR:εR≤δDeep) (hεRsample:εR≤εsample)
    (hεH0:0≤εH) (hεH:εH≤δDeep) (hεHsample:εH≤εsample)
    (hβe0:0≤eParent*ε) (hβecap:eParent*ε≤cBoundary*ε)
    (hβh0:0≤hParentRate*ε) (hβhcap:hParentRate*ε≤cBoundary*ε)
    (hεRinitial:εR≤δInitial) (hεHinitial:εH≤δInitial) (hηInitial:ηInitial≤ηbal)
    (hcut:δcut≤min (αcut/32) (pstar/512)) (hhref:href≤αcut*pstar/64)
    (hBhost:0≤Bhost) (hpstar:0<pstar) (hζparent:0≤ζparent) (hN₀:1≤N₀)
    (hscale:OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH Bhost (ρ₀/16) pstar βparent εparent ζparent rateParent N₀)
    (hroot:OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad mWheel k loadK (Nat.le_trans (Nat.le_succ 2) hmWheel) α βparent cParent
      (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*hParent-ζparent) δparent εparent (ρ₀/16) gapParent lamRoot)
    (hξroot:0≤ξroot) (haLoad:0≤aLoad) (hηbal:0≤ηbal) (hcParent:0≤cParent)
    (hlam:0≤lamGeo) (hlam1:lamGeo≤1/4) (hlamRoot:lamGeo≤lamRoot)
    (hNcert:Ncert≤N) (hNsize:2/ε≤N) (hterminal:(N:ℝ)≤ε*mv/2)
    (hN₀N:N₀≤N) (hMN:M≤N)
    (hδend:0≤δend) (hRend:εR≤δend/4) (hHend:εH≤δend/4) (hRateEnd:rateParent≤δend*ε/8) (hRate0:0≤rateParent)
    (hζhub:0<ζhub) (hζlocal:0<ζlocal) (hγcert:0<γcert) (hγe:γcert≤eParent)
    (hκ:κ≤ρ₀/8) (hθmatch:0<θmatch)
    (hθeq:θmatch=cMatch*ε)
    (hcMatch:cMatch≤min (ζhub*γcert*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2)
    (hζparentLe:ζparent≤hParent) (hGeomSlack:2*geomCap≤hParent/2)
    (hξGeom:ξreserve≤geomCap) (hζGeom:ζout≤geomCap)
    (hεsup:εsup≤p^2/4) (hpθ:p≤4*θmatch) (hsqrt:20*Real.sqrt (2*p)≤θmatch/2)
    (hell:max (18*aLoad+3*(((loadK:ℝ)+1)*lamGeo)) ((3*aLoad+lamGeo)*((mWheel:ℝ)+1))≤ellCap)
    (hcoverCap:10*ξroot≤finishCap)
    (hsched:OrdinaryAsymmetricFinishSchedule mWheel Nfinish eParent hParentRate ε βeGeo βhGeo θmatch p δsample ellCap finishCap kcap rate ν cap)
    (bDeep BweightDeep ξdeep Kdom loss χinner χdeep χone χtwo χcut χhost:ℝ)
    (selection:OrdinaryGeneralFullDomainSelection mWheel k d hmWheel hd
      (max (1/2) (cycleThreshold (mWheel+1))) α pstar (ρ₀/16) βP ηP row ηH βH cParent Bhost εTri χhost (2*(3*d)) hpstar
      (Fin n) (Fin q) Bool Bool (markedVortexVertexType Q) (markedVortexHubType Q) P (permutationConflictGraph π (3*d))
      (fun i=>(markedVortexVertexEmbedding Q i).toEmbedding) (fun i=>markedVortexHubEmbedding Q i) (markedVortexPermutation Q π hπ) (Q.length-1))
    (hinputs:∀i,i<Q.length→OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
      (P.comap (markedVortexVertexEmbedding Q i).toEmbedding) ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i).toEmbedding)
      (markedVortexPermutation Q π hπ i) (markedVortexInnerHubs Q i) (2*pRaw) pH
      (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity (Fin q) D) β)
    (hFs:∀u,(Fs u).IsRegularOfDegree 2) (hsize:∀u (c:↥(Comps u)),Fintype.card c.val=mWheel+1)
    (K:ℕ) (i₀:Fin K) (rsv θsample cSample smin:ℝ) (hsmin:0<smin)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) Fs hFs K i₀ rsv θsample cSample ρ₀ smin d)
    (hpstarEq:pstar=ρ₀*smin/2) (hpRawEq:pRaw=initialIndexDensity (Fin q) D*rsv/2) (hpHEq:pH=rsv)
    (hspEq:sp=ordinaryAssignedSpokeProbability Fs hFs K i₀ rsv θsample cSample)
    (ηedit ηBudget cInitial δedit:ℝ)
    (hεRedit:εR≤δedit) (hεHedit:εH≤δedit)
    (hβeInitial:eParent*ε≤cInitial*ε) (hβhInitial:hParentRate*ε≤cInitial*ε)
    (hβα:β≤2*α) (hηle:ηBudget≤ηedit) (hζ0:0≤ζ) (hsmall:15*ηBudget≤ζ*ε/2)
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
    let Good:=OrdinaryDeepRowsCutsEvent n q D mv mWheel loadK d β ε P Q π hπ pRaw pH pstar αcut cHub CHub
      bDeep BweightDeep ξdeep ηHub Kdom a aLoad ρdeep θdeep capHub eParent hParentRate εR εH
      (fun _=>θhost+α-β/2) (fun i=>εR*(markedVortexInnerVertices Q i).card) (fun i=>εH*(markedVortexInnerHubs Q i).card)
      sp false Rextra μ νextra Prior loss χinner χdeep χone χtwo χcut
    let All:=OrdinaryVortexParentProductEvent n q D mv mWheel k d (Q.length-1) hmWheel hd β ε α ρ₀ pstar
      βP ηP row ηH βH cParent Bhost εTri χhost δparent hParent hpstar P Q π hπ selection pRaw pH sp false Rextra Good
    let Bad:=permutationConflictGraph π (3*d)
    let Bweight:=4*CHub/pstar^(3*mWheel+1)
    let cert:=ordinarySelectedParentCertificateParameters mWheel loadK k d n₀ Nclean Nreserve Ncert hmWheel
      α ρ₀ pstar βout cParent Bhost hParent δparent εparent gapParent geomGap
      ηpack γcert cHub Bweight pstar κ ηHub ζhub ζlocal δend p βeGeo βhGeo ν cap εsup δsample τ εout
    OrdinaryVortexFineCertificateAtGeneralLoad cert→
    max (max (max (4*cert.n₀) (4*cert.Nreserve)) (max cert.Nclean 64)) (max cert.Ncert Nfinish)≤M→
    cert.L≤kcap^2*M→
    ∀z,All z∧Extra z→ Prior z ∧
      ((let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)
      let Reference:=rawWheelGraph P raw\Bad
      let Href:=rawWheelSpokes π d raw false;
    (∀Kres JQ JH,OrdinaryCorrectedProtectedReservoirWitness (mWheel+1) mAbs tAbs aAbs bAbs ξabs Reference Bad Href
      Ares (Q.extendedVertices 1) Wterm Bterm (Q.extendedIndices 1) Kres JQ JH→
      0≤Cost Kres ∧ Cost Kres≤14*ηBudget*n ∧ Cost Kres+2*((3*d:ℕ):ℝ)≤15*ηBudget*n))→
      OrdinaryGeneralUniformMatchedWheelOutcome (mAbs:=mAbs) (tAbs:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
        (mWheel+1) d P D mv β ε rate ξroot Q π Fs Comps Ares Wterm Bterm ξabs Cost z.1.1) :=by
  intro Good All Bad Bweight cert hcert hbase hbudget z hz
  have hcMatch':cMatch≤min (cert.ζhub*cert.γ*(1/4:ℝ)) (cert.ζlocal*(1/4:ℝ))/2:=by
    simpa [cert,ordinarySelectedParentCertificateParameters] using hcMatch
  have hBounds:=ordinary_selected_parent_certificate_bounds cert hParent ζparent geomCap ξreserve ζout ε cMatch θmatch
    (by rfl) hζparentLe hGeomSlack hξGeom hζGeom hε.le hθeq hcMatch'
  have hpack:=hBounds.1
  have hθcap:θmatch≤(min (ζhub*γcert*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2)*ε:=by
    simpa [cert,ordinarySelectedParentCertificateParameters] using hBounds.2
  have hD:0<D:=by
    have hnreal:(0:ℝ)<Fintype.card (Fin n):=by exact_mod_cast hn
    have hDreal:0<(D:ℝ):=lt_of_lt_of_le (half_pos hnreal) hhalf
    exact_mod_cast hDreal
  obtain ⟨hps,hpRlo,hpRhi,hprsv,hrsv0,hrsv1,hmean,hspfalse⟩:=
    ordinary_assigned_wheel_sample_inputs Fs hFs P hreg hD K i₀ rsv θsample cSample ρ₀ smin d hρ hρlo hρhi hsmin sampling
  have hpR:pstar≤2*pRaw:=by rw [hpstarEq,hpRawEq];exact hpRlo
  have hpR1:2*pRaw≤1:=by rw [hpRawEq];exact hpRhi
  have hpH:pstar≤pH:=by rw [hpstarEq,hpHEq];exact hprsv
  have hpHpos:0<pH:=by rw [hpHEq];exact hrsv0
  have hpH1:pH≤1:=by rw [hpHEq];exact hrsv1
  have hpEq:2*pRaw=initialIndexDensity (Fin q) D*pH:=by rw [hpRawEq,hpHEq];exact hmean
  have hsp:∀u,sp u false=pH:=by intro u;rw [hspEq,hpHEq];exact hspfalse u
  have hlevelsize:∀i,i<Q.length→N₀≤Fintype.card (markedVortexVertexType Q i) ∧ M≤(markedVortexInnerVertices Q i).card:=by
    intro i hi
    have h:=ordinary_triangle_all_level_size_from_terminal P D mv β ε ρ₀ Q hreg hn hhalf hρ hρlo hρhi hβ0 hβ1 hε hmv N₀ N hN₀N hNsize hterminal i hi
    exact ⟨h.1,hMN.trans h.2⟩
  have hEventLevels:=ordinary_wheel_selected_sample_level_from_common n q D mv mWheel loadK k d hmWheel hd β ε P Q π hπ
    α ρ₀ pstar βP ηP row ηH βH cParent Bhost εTri χhost δparent hParent hpstar selection
    pRaw pH pstar αcut cHub CHub bDeep BweightDeep ξdeep ηHub Kdom a aLoad ρdeep θdeep capHub eParent hParentRate εR εH
    (fun _=>θhost+α-β/2) (fun i=>εR*(markedVortexInnerVertices Q i).card) (fun i=>εH*(markedVortexInnerHubs Q i).card)
    sp false Rextra μ νextra Prior loss χinner χdeep χone χtwo χcut z hinputs hz.1
  obtain ⟨hPrior,hLevels⟩:=hEventLevels
  refine ⟨hPrior,?_⟩
  intro hCost
  unfold OrdinaryGeneralUniformMatchedWheelOutcome
  intro raw Bad' Reference Href Kres JQ JH hw Target hTargetP hTarget embed hf
  exact ordinary_uniform_tracked_split_from_payload (mAbs:=mAbs) (tAbs:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
    mWheel loadK d k hmWheel hk ρ₀ pstar href δcut ζcut εcut ζlimit εsample
    ε ξroot aLoad a ρdeep θdeep β ηbal ηProfile α ζ cBoundary δDeep rate rateParent ηInitial δInitial
    hrate hζlim hζrate hζcut hεcut hζlimit
    P D mv Q π hπ z.1.1 z.2 sp Fs Comps Ares Wterm Bterm ξabs Cost
    (2*pRaw) pH θhost εR εH αcut cHub CHub ηHub capHub eParent hParentRate
    βP ηP row ηH βH cParent Bhost εTri βparent δparent hParent εparent gapParent ζparent lamRoot N₀
    βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap
    δend ζhub ζlocal γcert κ ν cap εsup δsample τ n₀ Nclean Nreserve Ncert Nfinish M N θmatch ellCap finishCap kcap
    hreg hn hhalf hρ hρlo hρhi hβ0 hβ1 hε hmv hζcap hpR hpR1 hpH hpH1 hθhost hdegree hpEq hsp
    hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβecap hβh0 hβhcap hεRinitial hεHinitial hηInitial hpHpos hcut hhref
    hBhost hpstar hζparent hN₀ hscale hroot hξroot haLoad hηbal hcParent hlam hlam1 hlamRoot
    hNcert hNsize hterminal hlevelsize hδend hRend hHend hRateEnd hRate0 hζhub hζlocal hγcert hγe hκ hθmatch hθcap hεsup hpθ hsqrt hell hcoverCap hsched (selection.weight)
    hFs hsize ηedit ηBudget cInitial δedit hεRedit hεHedit hβeInitial hβhInitial hβα hηle hζ0 hsmall
    hgeometryRoot hγgeom hlamρ hξreserve hεξ hερ hεroot hβeGeo hβhGeo hedit hβcap hRcap hHcap hξcap haCap hbalCap hrowCap hlevel haEdit hlamE hlamH
    m₀ Nmin Nextra hm₀ hNmin hpayload hcert
    (by intro i hi; convert hLevels i hi using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    hpack hbase hbudget
    (by
      intro Kres JQ JH hw
      apply hCost Kres JQ JH
      convert hw using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    Kres JQ JH
    (by convert hw using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    Target hTargetP hTarget embed hf
end Oberwolfach
