module

public import Oberwolfach.OrdinaryTrackedInitialCertificateFromSample
public import Oberwolfach.OrdinaryWheelSelectedSampleLevelData

@[expose] public section
/-! The initial tracked certificate consumes level zero of the same common
sample data used by later-history certificates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

theorem ordinary_tracked_initial_from_sample_level {n q mWheel mAbs t aAbs bAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsize:∀u (c:↥(C u)),Fintype.card c.val=mWheel+1)
    (hS:S.IsRegularOfDegree (2*q)) (hSP:S≤P)
    (Inner Z Wterm A:Finset (Fin n)) (Hubs Bprotect Bterm:Finset (Fin q)) (ξ:ℝ)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (D mv mEdit Nedit:ℕ) (β ε θ α ρ₀ pmin hmin bal cBoundary δ ηedit ηBudget ζcert capHub:ℝ)
    (Vor:Vortex (Fin q) P D β ε mv) (hπ:∀i x,π x∈Vor.extendedVertices i↔x∈Vor.extendedVertices i)
    (hn:0<n) (hN:Nedit≤n) (hmEdit:mEdit≤mv) (hmv:0<mv) (hε:0<ε)
    (hreg:P.IsRegularOfDegree D) (hhalf:(n:ℝ)/2≤D) (hρ₀:0<ρ₀)
    (hρlo:ρ₀≤ initialIndexDensity (Fin q) D) (hρhi:initialIndexDensity (Fin q) D≤1)
    (hβ:0≤β) (hβα:β≤2*α) (hθ:1/2≤θ) (hdegree:(θ+α)*(n:ℝ)≤D)
    (hηle:ηBudget≤ηedit) (hζ:0≤ζcert) (hζcap:ζcert≤capHub)
    (hsmall:15*ηBudget≤ζcert*ε/2) (hcost0:0≤cost) (hcost:cost≤14*ηBudget*n)
    (hconf:cost+2*((3*d:ℕ):ℝ)≤15*ηBudget*n)
    (hMargins:OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε bal cBoundary δ ηedit β d mEdit Nedit)
    (pR pH εR εH βe βh b Bweight ηHub:ℝ) (sp:Fin q→Bool→ℝ)
    (hpR:pmin≤pR) (hpR1:pR≤1) (hpH:hmin≤pH) (hpR0:0≤pR) (hpH0:0≤pH)
    (hεR:0≤εR) (hεRδ:εR≤δ) (hεH:0≤εH) (hεHδ:εH≤δ)
    (hβe:0≤βe) (hβecap:βe≤cBoundary*ε) (hβh:0≤βh) (hβhcap:βh≤cBoundary*ε)
    (hpEq:pR=initialIndexDensity (Fin q) D*pH) (hsp:∀u,sp u false=pH)
    (loadK mFine:ℕ) (href a ρdeep θdeep δcut ζcut εcut ζlimit εsample ξroot aLoad αcut pstar:ℝ)
    (hFine:OrdinaryInitialFineCoverFromSharedAt mWheel loadK d ρ₀ hmin href a ρdeep θdeep δcut ζcut εcut ζlimit εsample ε ξroot aLoad bal αcut pstar β mFine)
    (hmFine:mFine≤mv) (hβ1:β≤1/4) (hpH1:pH≤1) (hpHpos:0<pH)
    (hεRsample:εR≤εsample) (hεHsample:εH≤εsample) (hζlimit:ζcert≤ζlimit) (coins:Sym2 (Fin n)→Bool)
    (k N₀ Ncert N:ℕ) (hmWheel:3≤mWheel) (hk:4≤k)
    (βH ηH Bhost βparent εparent ζparent rateParent cParent hParent δparent gapParent lamRoot:ℝ)
    (hBhost:0≤Bhost) (hpstar:0<pstar) (hζparent:0≤ζparent) (hN₀:1≤N₀)
    (hscale:OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH Bhost (ρ₀/16) pstar βparent εparent ζparent rateParent N₀)
    (hroot:OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad mWheel k loadK (Nat.le_trans (Nat.le_succ 2) hmWheel) α βparent cParent
      (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*hParent-ζparent) δparent εparent (ρ₀/16) gapParent lamRoot)
    (βP ηP row εTri:ℝ)
    (weight:OrdinaryCycle (P.comap (markedVortexVertexEmbedding Vor 0)) (mWheel+1)→ℝ)
    (lamGeo γgeom edit βeGeo βhGeo βout ξreserve ζout pp ηpack εout geomGap:ℝ)
    (δend ζhub ζlocal γcert eParent:ℝ)
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad s)
    (hs_m:s.m=mWheel) (hs_k:s.k=k) (hs_load:s.loadK=loadK) (hs_α:s.α=α) (hs_ω:s.ω=ρ₀/16)
    (hs_β:s.β=βout) (hs_bRoot:s.bRoot=cParent*(1-δparent)^mWheel)
    (hs_BRoot:s.BRoot=Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (hs_δ:s.δ=δparent/2)
    (hs_εstar:s.εstar=(εparent+gapParent)+geomGap) (hs_ηpack:s.ηpack=ηpack)
    (hs_p:s.p=pp) (hs_εgeom:s.εgeom=εout) (hs_βe:s.βe=βeGeo) (hs_βh:s.βh=βhGeo)
    (hs_bHub:s.bHub=b) (hs_BHub:s.BHub=Bweight) (hs_ηhub:s.ηhub=ηHub)
    (hs_Ncert:s.Ncert=Ncert) (hs_δend:s.δend=δend) (hs_ζhub:s.ζhub=ζhub)
    (hs_ζlocal:s.ζlocal=ζlocal) (hs_γ:s.γ=γcert)
    (hParentRate:ℝ) (hβeEq:βe=eParent*ε) (hβhEq:βh=hParentRate*ε)
    (hb₀:(2*(3*d):ℕ)≤s.b₀) (hLconf:(2*((3*d:ℕ):ℝ))≤s.L)
    (hpack:s.hpack≤(2*hParent-ζparent)-ξreserve-ζout) (hκ:s.κ≤ρ₀/8)
    (hp₀R:s.p₀≤pR) (hp₀H:s.p₀≤pH)
    (Nfinish M:ℕ) (rate θmatch ellCap finishCap kcap:ℝ)
    (hθmatch:0<θmatch) (hθcap:θmatch≤(min (s.ζhub*s.γ*(1/4:ℝ)) (s.ζlocal*(1/4:ℝ))/2)*ε)
    (hεsup:s.εsup≤s.p^2/4) (hpθ:s.p≤4*θmatch) (hsqrt:20*Real.sqrt (2*s.p)≤θmatch/2)
    (hbase:max (max (max (4*s.n₀) (4*s.Nreserve)) (max s.Nclean 64)) (max s.Ncert Nfinish)≤M)
    (hM:M≤(markedVortexInnerVertices Vor 0).card)
    (hell:max (18*aLoad+3*(((s.loadK:ℝ)+1)*lamGeo)) ((3*aLoad+lamGeo)*((s.m:ℝ)+1))≤ellCap)
    (hcover:10*ξroot≤finishCap) (hbudget:s.L≤kcap^2*M)
    (hsched:OrdinaryAsymmetricFinishSchedule s.m Nfinish eParent hParentRate ε s.βe s.βh θmatch s.p s.δsample ellCap finishCap kcap rate s.ν s.cap) (CHub:ℝ) (hpmin:pmin=pstar) (hBweight:Bweight=4*CHub/pmin^(3*mWheel+1)):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e)
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P raw\Bad
    let Href:=rawWheelSpokes π d raw false
    let Q:=S\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u)
    let Gstart:=Q\ordinaryResourceRim Q K
    let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
    letI : DecidableEq (markedVortexVertexType Vor 0):=Classical.decEq _
    letI : DecidableEq (markedVortexHubType Vor 0):=Classical.decEq _
    let I:=markedVortexInnerVertices Vor 0;let B:=markedVortexInnerHubs Vor 0;
    let fv:(markedVortexVertexType Vor 0)↪Fin n:=(markedVortexVertexEmbedding Vor 0).toEmbedding;
    let gu:=markedVortexHubEmbedding Vor 0;
    let ρ:=markedVortexPermutation Vor π hπ 0;let rawLocal:=ordinaryRawRestrictPair fv gu raw;
    let Gloc:=Gstart.comap fv;let Floc:=Bad.comap fv;let Hloc:=fun v u=>Hstart (fv v) (gu u);
    let L:=cost+2*((3*d:ℕ):ℝ);
    OrdinaryCorrectedProtectedReservoirWitness (mWheel+1) mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm Bprotect K JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f→
    OrdinaryWheelSelectedSampleLevelData n q D mv mWheel loadK k d hmWheel β ε P Vor π hπ
      α ρ₀ pstar βP ηP row ηH βH cParent Bhost εTri δparent hParent
      pR pH pmin αcut b CHub ηHub a aLoad ρdeep θdeep capHub eParent hParentRate εR εH
      (fun _=>θ+α-β/2) (fun t=>εR*(markedVortexInnerVertices Vor t).card)
      (fun t=>εH*(markedVortexInnerHubs Vor t).card) sp false raw coins 0 weight→
    0≤bal→N₀≤Fintype.card (markedVortexVertexType Vor 0)→ζcert≤rateParent→0≤rateParent→
    pstar≤pR→pstar≤pH→0≤cParent→
    OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (mWheel+1) k 2 ρ₀ (βparent/2)
      (cParent*(1-δparent)^mWheel) (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (εparent+gapParent) geomGap
      βout ξreserve ζout edit pp ηpack εout γgeom→
    0<γgeom→0≤lamGeo→lamGeo≤lamRoot→lamGeo≤1/4→lamGeo≤(ρ₀/8)/2→0≤ξreserve→
    ε≤ξreserve/2→ε≤ξreserve*(ρ₀/8)/2→2*ε^2≤lamGeo→
    0≤βeGeo→0≤βhGeo→0≤ξroot→0≤aLoad→0<edit→
    β≤γgeom/1000→εR≤γgeom/1000→εH≤γgeom/1000→ξroot≤γgeom/160000→
    aLoad≤γgeom/1000→bal≤γgeom/1000→
    3*(((loadK:ℝ)+1)*lamGeo)≤edit/4→lamGeo*((mWheel:ℝ)+1)≤edit/4→
    aLoad≤edit/(72*((mWheel:ℝ)+2))→lamGeo≤βeGeo/4→lamGeo≤βhGeo/2→
    Ncert≤N→2/ε≤(N:ℝ)→(N:ℝ)≤ε*mv/2→0≤δend→
    εR≤δend/4→εH≤δend/4→ rateParent≤δend*ε/8→
    0<ζhub→0<ζlocal→0<γcert→γcert≤eParent→
    let T:=ordinaryVortexBufferedVertices Vor 0 2;let W:=ordinaryVortexBufferedHubs Vor 0 2;
    let bin:=bal*I.card;
    let deep:ℝ:=(initialIndexDensity (Fin q) D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*L;
    let cover:=10*ξroot*I.card;let loss:=12*aLoad*Fintype.card (markedVortexVertexType Vor 0);
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Vor 0)+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Vor 0)*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    OrdinaryWheelLikelySeparateCostsCertificate Gloc Floc Hloc I T B W (mWheel+1)
      (rate*Fintype.card (markedVortexVertexType Vor 0⊕markedVortexHubType Vor 0)) cover :=by
  intro raw Bad Reference Href Q H Gstart Hstart I B fv gu ρ rawLocal Gloc Floc Hloc L hw hf hsample
    hbal0 hNlocal hζrate hRate0 hpRstar hpHstar hcParent hgeometry
    hγ hlam hlamRoot hlam1 hlamρ hξreserve hεξ hερ hεroot hβeGeo hβhGeo hξroot haLoad hedit
    hβcap hRcap hHcap hξcap haCap hbalCap hrowCap hlevel haEdit hlamE hlamH
    hNcert hNsize hterminal hδend hRend hHend hRateEnd hζhub hζlocal hγcert heParent
    T W bin deep cover loss ell
  dsimp only [OrdinaryWheelSelectedSampleLevelData] at hsample
  obtain ⟨hfamily,hdeepEvent,hrow,htwo,hrim,hevent,hcuts,hinputs,hweight⟩:=hsample
  rw [←hβeEq,←hβhEq,←hBweight] at hfamily
  rw [hpmin] at hrim
  have hh:=ordinary_tracked_initial_certificate_from_sample (mAbs:=mAbs) (t:=t) (aAbs:=aAbs) (bAbs:=bAbs) P S π d σ Fs hFs C hsize hS hSP
    Inner Z Wterm A Hubs Bprotect Bterm ξ K JQ JH cost f D mv mEdit Nedit β ε θ α ρ₀ pmin hmin bal cBoundary δ ηedit ηBudget ζcert capHub
    Vor hπ hn hN hmEdit hmv hε hreg hhalf hρ₀ hρlo hρhi hβ hβα hθ hdegree hηle hζ hζcap hsmall hcost0 hcost hconf hMargins
    pR pH εR εH βe βh b Bweight ηHub sp hpR hpR1 hpH hpR0 hpH0 hεR hεRδ hεH hεHδ hβe hβecap hβh hβhcap hpEq hsp
    loadK mFine href a ρdeep θdeep δcut ζcut εcut ζlimit εsample ξroot aLoad αcut pstar hFine hmFine hβ1 hpH1 hpHpos hεRsample hεHsample hζlimit coins
    k N₀ Ncert N hmWheel hk βH ηH Bhost βparent εparent ζparent rateParent cParent hParent δparent gapParent lamRoot
    hBhost hpstar hζparent hN₀ hscale hroot βP ηP row εTri weight
    lamGeo γgeom edit βeGeo βhGeo βout ξreserve ζout pp ηpack εout geomGap δend ζhub ζlocal γcert eParent
    s hcert hs_m hs_k hs_load hs_α hs_ω hs_β hs_bRoot hs_BRoot hs_δ hs_εstar hs_ηpack hs_p hs_εgeom
    hs_βe hs_βh hs_bHub hs_BHub hs_ηhub hs_Ncert hs_δend hs_ζhub hs_ζlocal hs_γ
    hParentRate hβeEq hβhEq hb₀ hLconf hpack hκ hp₀R hp₀H Nfinish M rate θmatch ellCap finishCap kcap
    hθmatch hθcap hεsup hpθ hsqrt hbase hM hell hcover hbudget hsched
    (by convert hw using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hf using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hrow using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert htwo using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hfamily using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hdeepEvent using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hrim using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hbal0 hNlocal hζrate hRate0
    (by convert hinputs using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hpRstar hpHstar hcParent
    (by convert hweight using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hevent using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hcuts using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _) hgeometry
    hγ hlam hlamRoot hlam1 hlamρ hξreserve hεξ hερ hεroot hβeGeo hβhGeo hξroot haLoad hedit
    hβcap hRcap hHcap hξcap haCap hbalCap hrowCap hlevel haEdit hlamE hlamH hNcert hNsize hterminal hδend hRend hHend hRateEnd hζhub hζlocal hγcert heParent
  convert hh using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
end Oberwolfach
