module

public import Oberwolfach.OrdinaryTrackedInitialTriangleFineFromSample
public import Oberwolfach.OrdinaryTrackedInitialSharpPairingFromSample
public import Oberwolfach.OrdinaryInitialTriangleSharpFromStaticGeometry
public import Oberwolfach.OrdinaryInitialPairingFromInnerEdit

@[expose] public section
/-! The tracked matching remainder retains its host, balances, initial sharp
reference, profile, hub weights and pairing geometry on the common sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_initial_triangle_sharp_bundle_from_sample {n q mAbs t aAbs bAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsize:∀u (c:↥(C u)),Fintype.card c.val=2+1)
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
    (mFine:ℕ) (href κFine δcut ζcut εcut ζlimit εsample ξroot aLoad αcut pstar:ℝ)
    (hFine:OrdinaryInitialTriangleFineCoverFromSharedAt d ρ₀ hmin href κFine δcut ζcut εcut ζlimit εsample ε ξroot aLoad bal αcut pstar β mFine)
    (hmFine:mFine≤mv) (hβ1:β≤1/4) (hpH1:pH≤1) (hpHpos:0<pH)
    (hεRsample:εR≤εsample) (hεHsample:εH≤εsample) (hζlimit:ζcert≤ζlimit) (coins:Sym2 (Fin n)→Bool)
    (k N₀ Ncert N:ℕ) (hk:4≤k)
    (βH ηH Bhost βparent εparent ζparent rateParent cParent hParent δparent gapParent lamRoot:ℝ)
    (hBhost:0≤Bhost) (hpstar:0<pstar) (hζparent:0≤ζparent) (hN₀:1≤N₀)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH Bhost (ρ₀/16) pstar βparent εparent ζparent rateParent N₀)
    (hroot:OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad 2 k 0 (by decide) α βparent cParent
      (Bhost/((ρ₀/16)*pstar^(2*(2+1)-1))) (2*hParent-ζparent) δparent εparent (ρ₀/16) gapParent lamRoot)
    (βP ηP εTri:ℝ)
    (weight:OrdinaryCycle (P.comap (markedVortexVertexEmbedding Vor 0)) (2+1)→ℝ)
    (lamGeo γgeom edit βeGeo βhGeo βout ξreserve ζout pp ηpack εout geomGap:ℝ)
    (δend ζhub ζlocal γcert eParent:ℝ):
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
    OrdinaryCorrectedProtectedReservoirWitness (2+1) mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm Bprotect K JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P Bad D mv β ε Vor π hπ pR pH sp false raw→
    OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P Bad D mv β ε Vor π hπ pR pH sp false raw→
    OrdinaryUniformInnerHubEvent 2 P D mv d β ε Vor π hπ pR pH βe βh b Bweight ηHub capHub
      (fun _=>θ+α-β/2) (fun k=>εR*(markedVortexInnerVertices Vor k).card)
      (fun k=>εH*(markedVortexInnerHubs Vor k).card) sp false raw→
    OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κFine aLoad P D mv β ε Vor π hπ false raw→
    OrdinaryInducedRimCutEvent (Vor.extendedVertices 1) (sampledOrientation (rawWheelGraph P raw) coins) αcut pstar→
    0≤bal→N₀≤Fintype.card (markedVortexVertexType Vor 0)→ζcert≤rateParent→0≤rateParent→
    OrdinaryDeepCoverLevelInputs 2 (2*(3*d)) d α pstar (ρ₀/16) 1 εTri (P.comap fv) Floc ρ B pR pH
      (2*(Fintype.card (markedVortexHubType Vor 0):ℝ)/initialIndexDensity (Fin q) D) β→
    pstar≤pR→pstar≤pH→0≤cParent→
    (∀C,cParent/(Fintype.card (markedVortexVertexType Vor 0):ℝ)^((2+1)-2)≤weight C ∧
      weight C≤Bhost/(Fintype.card (markedVortexVertexType Vor 0):ℝ)^((2+1)-2))→
    ordinaryCombinedTriangleEvent d k (P.comap fv) Floc ρ (max (1/2) (cycleThreshold 3)) α pstar
      βP ηP ηH βH cParent Bhost pR pH weight false rawLocal→
    OrdinaryTriangleReferenceNormalizedCuts (P.comap fv) Floc ρ d false δparent hParent rawLocal
      (fun e=>coins (Sym2.map fv e))→
    OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (2+1) k 2 ρ₀ (βparent/2)
      (cParent*(1-δparent)^2) (Bhost/((ρ₀/16)*pstar^(2*(2+1)-1))) (εparent+gapParent) geomGap
      βout ξreserve ζout edit pp ηpack εout γgeom→
    0<γgeom→0≤lamGeo→lamGeo≤lamRoot→lamGeo≤1/4→lamGeo≤(ρ₀/8)/2→0≤ξreserve→
    ε≤ξreserve/2→ε≤ξreserve*(ρ₀/8)/2→2*ε^2≤lamGeo→
    0≤βeGeo→0≤βhGeo→0≤ξroot→0≤aLoad→0<edit→
    β≤γgeom/1000→εR≤γgeom/1000→εH≤γgeom/1000→ξroot≤γgeom/160000→
    aLoad≤γgeom/1000→bal≤γgeom/1000→
    3*(((0:ℝ)+1)*lamGeo)≤edit/4→lamGeo*((2:ℝ)+1)≤edit/4→
    aLoad≤edit/(72*((2:ℝ)+2))→lamGeo≤βeGeo/4→lamGeo≤βhGeo/2→
    Ncert≤N→2/ε≤(N:ℝ)→(N:ℝ)≤ε*mv/2→0≤δend→
    εR≤δend/4→εH≤δend/4→ rateParent≤δend*ε/8→
    0<ζhub→0<ζlocal→0<γcert→γcert≤eParent→
    let T:=ordinaryVortexBufferedVertices Vor 0 2;let W:=ordinaryVortexBufferedHubs Vor 0 2;
    let bin:=bal*I.card;
    let deep:ℝ:=(initialIndexDensity (Fin q) D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*L;
    let cover:=10*ξroot*I.card;let loss:=12*aLoad*Fintype.card (markedVortexVertexType Vor 0);
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Vor 0)+3*((W.card:ℝ)+((0:ℝ)+1)*T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Vor 0)*((2:ℝ)+1)+(T.card:ℝ)*((2:ℝ)+1));
    Gstart≤P\Bad ∧
    (∀v,Gstart.degree v=2*(Finset.univ.filter (Hstart v)).card) ∧
    (∀u,3∣(Finset.univ.filter (fun v=>Hstart v u)).card) ∧
    L≤ζcert*I.card ∧
    OrdinaryCleanupParentProfiles (P.comap fv) Gloc Floc Hloc ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh (fun u=>sp (gu u)) false rawLocal ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale 2 b Bweight ηHub Gloc Floc Hloc I B) ∧
    OrdinaryVortexAsymmetricPairingGeometryAt Vor 0 Ncert ρ₀ δend εR εH L ζhub ζlocal γcert eParent ∧
    (T.card:ℝ)≤(βeGeo/4)*Fintype.card (markedVortexVertexType Vor 0⊕markedVortexHubType Vor 0) ∧
    (W.card:ℝ)≤(βhGeo/2)*Fintype.card (markedVortexVertexType Vor 0⊕markedVortexHubType Vor 0) ∧
    (T.card:ℝ)+W.card≤lamGeo*Fintype.card (markedVortexVertexType Vor 0) ∧
    ∃Root:OrdinaryRootCoverNonrootData Gloc Floc Hloc I T B W (2+1) cover ell,
      Nonempty (OrdinaryRootCoverSharpReferenceData (P.comap fv) Gloc Floc Hloc I T B W (2+1) k (by omega)
        cover ell bin bin deep loss Root α (ρ₀/16) (βparent/2) βout (cParent*(1-δparent)^2)
        (Bhost/((ρ₀/16)*pstar^(2*(2+1)-1))) (2*hParent-ζparent) (δparent/2) (εparent+gapParent)
        ((εparent+gapParent)+geomGap) ηpack ξreserve ζout pp εout
        (deep+2*cover) (bin+deep+4*cover) (bin+deep+loss)) :=by
  intro raw Bad Reference Href Q H Gstart Hstart I B fv gu ρ rawLocal Gloc Floc Hloc L hw hf hrow htwo hfamily hdeepEvent hrim
    hbal0 hNlocal hζrate hRate0 hinputs hpRstar hpHstar hcParent hweight hevent hcuts hgeometry
    hγ hlam hlamRoot hlam1 hlamρ hξreserve hεξ hερ hεroot hβeGeo hβhGeo hξroot haLoad hedit
    hβcap hRcap hHcap hξcap haCap hbalCap hrowCap hlevel haEdit hlamE hlamH
    hNcert hNsize hterminal hδend hRend hHend hRateEnd hζhub hζlocal hγcert heParent
    T W bin deep cover loss ell
  have htracked:=ordinary_tracked_initial_triangle_fine_from_sample P S π d σ Fs hFs C hsize hS hSP
    Inner Z Wterm A Hubs Bprotect Bterm ξ K JQ JH cost f D mv mEdit Nedit β ε θ α ρ₀ pmin hmin bal cBoundary δ ηedit ηBudget ζcert capHub
    Vor hπ hn hN hmEdit hmv hε hreg hhalf hρ₀ hρlo hρhi hβ hβα hθ hdegree hηle hζ hζcap hsmall hcost0 hcost hconf hMargins
    pR pH εR εH βe βh b Bweight ηHub sp hpR hpR1 hpH hpR0 hpH0 hεR hεRδ hεH hεHδ hβe hβecap hβh hβhcap hpEq hsp
    mFine href κFine δcut ζcut εcut ζlimit εsample ξroot aLoad αcut pstar hFine hmFine hβ1 hpH1 hpHpos hεRsample hεHsample hζlimit coins
    hw hf hrow htwo hfamily hdeepEvent hrim
  have hdecQ:(Classical.decEq (Fin q))=instDecidableEqFin q:=Subsingleton.elim _ _
  have hBufferedEq:
      @ordinaryVortexBufferedHubs (Fin n) (Fin q) _ _ (Classical.decEq (Fin q)) P D mv β ε Vor 0 2 =
      @ordinaryVortexBufferedHubs (Fin n) (Fin q) _ _ (instDecidableEqFin q) P D mv β ε Vor 0 2 :=by rw [hdecQ]
  have hInnerEq:
      @markedVortexInnerHubs (Fin n) (Fin q) _ _ (Classical.decEq (Fin q)) P D mv β ε Vor 0 =
      @markedVortexInnerHubs (Fin n) (Fin q) _ _ (instDecidableEqFin q) P D mv β ε Vor 0 :=by rw [hdecQ]
  have hdecQ':(fun (a b:Fin q)=>Classical.propDecidable (a=b))=instDecidableEqFin q:=Subsingleton.elim _ _
  have hInnerEq':
      @markedVortexInnerHubs (Fin n) (Fin q) _ _ (fun a b=>Classical.propDecidable (a=b)) P D mv β ε Vor 0 =
      @markedVortexInnerHubs (Fin n) (Fin q) _ _ (instDecidableEqFin q) P D mv β ε Vor 0 :=by rw [hdecQ']
  try rw [hdecQ] at htracked
  obtain ⟨hhost,hbal,hdiv,hLζ,hmargin,hphysical,hprofile,hnear,hcross,hdeep,hweights,hcover⟩:=htracked
  have hL0:0≤L:=by dsimp [L];positivity
  letI : DecidableRel Gstart.Adj:=fun v w=>Classical.propDecidable (Gstart.Adj v w)
  have hnearLocal:∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤bal*I.card:=by
    intro v
    convert hnear v using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  have hdecG:(fun v w:Fin n=>SimpleGraph.Sdiff.adjDecidable (Fin n) Q (ordinaryResourceRim Q K) v w)=
      (fun v w:Fin n=>Classical.propDecidable (Gstart.Adj v w)):=Subsingleton.elim _ _
  try rw [hdecG] at hnearLocal
  have hsharp:=ordinary_initial_triangle_sharp_from_static_geometry βH ηH Bhost ρ₀ pstar βparent εparent ζparent rateParent N₀
    hBhost hρ₀ hpstar hζparent hN₀ hscale k hk α cParent hParent δparent gapParent lamRoot hroot P Gstart Hstart D mv β ε Vor π hπ d false raw coins sp
    βP ηP εTri pR pH bal L ζcert hζrate hRate0 weight hreg (by simpa using hn) (by simpa using hhalf) hρlo hρhi hβ hβ1 hε hmv
    hNlocal hL0 hLζ hhost
    (by intro v;convert hbal v using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hinputs using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hpRstar hpR1 hpHstar hpH1 hcParent hweight
    (by convert hevent using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hcuts using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by intro z;convert hphysical z using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hbal0
    (by
      intro v
      have hh:=hnearLocal v
      dsimp only [I,B,Gloc,Hloc,fv,gu] at hh
      have hcounts:=ordinary_subtype_filter_card_of_equal_sets
        (@markedVortexInnerHubs (Fin n) (Fin q) _ _ (instDecidableEqFin q) P D mv β ε Vor 0)
        (@markedVortexInnerHubs (Fin n) (Fin q) _ _ (fun a b=>Classical.propDecidable (a=b)) P D mv β ε Vor 0)
        hInnerEq'.symm (fun u=>Hstart ((markedVortexVertexEmbedding Vor 0).toEmbedding v.val) ((markedVortexHubEmbedding Vor 0) u))
      have hcounts':
          (Finset.univ.filter (fun u:↥(@markedVortexInnerHubs (Fin n) (Fin q) _ _ (instDecidableEqFin q) P D mv β ε Vor 0)=>
            Hstart ((markedVortexVertexEmbedding Vor 0).toEmbedding v.val) ((markedVortexHubEmbedding Vor 0) u.val))).card =
          (Finset.univ.filter (fun u:↥(@markedVortexInnerHubs (Fin n) (Fin q) _ _ (fun a b=>Classical.propDecidable (a=b)) P D mv β ε Vor 0)=>
            Hstart ((markedVortexVertexEmbedding Vor 0).toEmbedding v.val) ((markedVortexHubEmbedding Vor 0) u.val))).card :=by
        convert hcounts using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
      rw [hcounts'] at hh
      convert hh using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hcross using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    ξroot aLoad lamGeo γgeom edit βeGeo βhGeo εR εH βout ξreserve ζout pp ηpack εout geomGap hgeometry hγ hlam hlamRoot hlam1 hlamρ
    hξreserve hεξ hερ hεroot hβeGeo hβhGeo hεR hεH hξroot haLoad hedit hβcap hRcap hHcap hξcap haCap hbalCap
    hrowCap hlevel haEdit hlamE hlamH
    (by convert hmargin using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hcover using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by intro v hv;convert hdeep v using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
  try rw [hdecQ] at hsharp
  have hpair:=ordinary_initial_pairing_from_inner_edit Vor hreg (by simpa using hn) (by simpa using hhalf)
    hρ₀ hρlo hρhi hβ hβ1 hε hmv Ncert N hNcert hNsize hterminal δend εR εH rateParent ζcert L hδend
    hRend hHend hRateEnd hRate0 hζ hζrate hLζ ζhub ζlocal γcert eParent hζhub hζlocal hγcert heParent
  refine ⟨?_,?_,?_,?_,?_,?_,hpair,?_⟩
  · convert hhost using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · intro v;convert hbal v using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · intro u;convert hdiv u using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · convert hLζ using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · convert hprofile using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · convert hweights using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · have hdecV:(Classical.decEq (markedVortexVertexType Vor 0))=
        (LinearOrder.toDecidableEq:DecidableEq (markedVortexVertexType Vor 0)):=Subsingleton.elim _ _
    have hdecU:(Classical.decEq (markedVortexHubType Vor 0))=
        (LinearOrder.toDecidableEq:DecidableEq (markedVortexHubType Vor 0)):=Subsingleton.elim _ _
    try simp only [hBufferedEq,hInnerEq] at hsharp ⊢
    try simp only [hdecQ,hdecV,hdecU] at hsharp ⊢
    try rw [hdecG]
    dsimp [T,W,bin,deep,cover,loss,ell,I,B,Gloc,Floc,Hloc,fv,gu,ρ,rawLocal,Bad,L]
    convert hsharp using 1 <;> congr! 10 <;> first | rfl | simp | (left; congr 1; ext x; simp [ordinaryVortexBufferedHubs,ordinaryVortexBufferedVertices]) | (ext x; simp [ordinaryVortexBufferedHubs,ordinaryVortexBufferedVertices]) | exact Subsingleton.elim _ _
    all_goals first | exact congrArg Finset.card hBufferedEq | exact congrArg Finset.card hBufferedEq.symm
end Oberwolfach
