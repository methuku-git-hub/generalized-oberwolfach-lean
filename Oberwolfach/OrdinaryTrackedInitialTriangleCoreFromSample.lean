module

public import Oberwolfach.OrdinaryTrackedInitialTriangleSharpFromSampleLevel
public import Oberwolfach.OrdinaryTriangleInitialLocalSharpInputs

@[expose] public section
/-! The actual matching remainder and level-zero common sample provide the
local sharp-input package for the root-free wheel certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_initial_triangle_core_from_sample {n q mAbs t aAbs bAbs:ℕ}
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
    (δend ζhub ζlocal γcert eParent:ℝ)
    (hαcut:αcut=min (α/4) (1/4:ℝ)) (hpminEq:pmin=pstar)
    (hpack cLinear τ ellCap finishCap:ℝ) (hηpack:ηpack=cLinear*τ):
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
    OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Vor π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bhost εTri δparent hParent
      pR pH pmin κFine aLoad εR εH b Bweight ηHub capHub βe βh
      (fun _=>θ+α-β/2) (fun i=>εR*(markedVortexInnerVertices Vor i).card)
      (fun i=>εH*(markedVortexInnerHubs Vor i).card) sp false raw coins 0 weight→
    0≤bal→N₀≤Fintype.card (markedVortexVertexType Vor 0)→ζcert≤rateParent→0≤rateParent→
    pstar≤pR→pstar≤pH→0≤cParent→
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
    0≤ellCap→0≤finishCap→
    max (18*aLoad+3*lamGeo) ((3*aLoad+lamGeo)*3)≤ellCap→10*ξroot≤finishCap→
    hpack≤(2*hParent-ζparent)-ξreserve-ζout→
    let T:=ordinaryVortexBufferedVertices Vor 0 2;let W:=ordinaryVortexBufferedHubs Vor 0 2;
    OrdinaryTriangleLocalSharpInputs (P.comap fv) Gloc Floc Hloc I T B W ρ d k (by omega)
      (fun u=>sp (gu u)) false rawLocal α (ρ₀/16) βout (cParent*(1-δparent)^2)
      (Bhost/((ρ₀/16)*pstar^(2*3-1))) hpack (δparent/2) ((εparent+gapParent)+geomGap) cLinear pp τ εout b Bweight ηHub
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L rateParent βe βh ξroot aLoad ellCap finishCap βeGeo βhGeo :=by
  intro raw Bad Reference Href Q H Gstart Hstart I B fv gu ρ rawLocal Gloc Floc Hloc L hw hf hsample
    hbal0 hNlocal hζrate hRate0 hpRstar hpHstar hcParent hgeometry
    hγ hlam hlamRoot hlam1 hlamρ hξreserve hεξ hερ hεroot hβeGeo hβhGeo hξroot haLoad hedit
    hβcap hRcap hHcap hξcap haCap hbalCap hrowCap hlevel haEdit hlamE hlamH
    hNcert hNsize hterminal hδend hRend hHend hRateEnd hζhub hζlocal hγcert heParent
    hellCap hfinishCap hell hξfinish hpackcut T W
  have hb:=ordinary_tracked_initial_triangle_sharp_from_sample_level (mAbs:=mAbs) (t:=t) (aAbs:=aAbs) (bAbs:=bAbs)
    P S π d σ Fs hFs C hsize hS hSP Inner Z Wterm A Hubs Bprotect Bterm ξ K JQ JH cost f
    D mv mEdit Nedit β ε θ α ρ₀ pmin hmin bal cBoundary δ ηedit ηBudget ζcert capHub
    Vor hπ hn hN hmEdit hmv hε hreg hhalf hρ₀ hρlo hρhi hβ hβα hθ hdegree hηle hζ hζcap hsmall hcost0 hcost hconf hMargins
    pR pH εR εH βe βh b Bweight ηHub sp hpR hpR1 hpH hpR0 hpH0 hεR hεRδ hεH hεHδ hβe hβecap hβh hβhcap hpEq hsp
    mFine href κFine δcut ζcut εcut ζlimit εsample ξroot aLoad αcut pstar hFine hmFine hβ1 hpH1 hpHpos hεRsample hεHsample hζlimit coins
    k N₀ Ncert N hk βH ηH Bhost βparent εparent ζparent rateParent cParent hParent δparent gapParent lamRoot
    hBhost hpstar hζparent hN₀ hscale hroot βP ηP εTri weight
    lamGeo γgeom edit βeGeo βhGeo βout ξreserve ζout pp ηpack εout geomGap δend ζhub ζlocal γcert eParent hαcut hpminEq
    hw hf hsample hbal0 hNlocal hζrate hRate0 hpRstar hpHstar hcParent hgeometry
    hγ hlam hlamRoot hlam1 hlamρ hξreserve hεξ hερ hεroot hβeGeo hβhGeo hξroot haLoad hedit
    hβcap hRcap hHcap hξcap haCap hbalCap hrowCap hlevel haEdit hlamE hlamH
    hNcert hNsize hterminal hδend hRend hHend hRateEnd hζhub hζlocal hγcert heParent
  obtain ⟨hhost,hbal,hdiv,hL,profile,hub,_pair,hT,hW,hroot,Root,hsharp⟩:=hb
  let bin:ℝ:=bal*I.card
  let deep:ℝ:=(initialIndexDensity (Fin q) D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*L
  let cover:ℝ:=10*ξroot*I.card
  let loss:ℝ:=12*aLoad*Fintype.card (markedVortexVertexType Vor 0)
  have hdecQ:(fun (a b:Fin q)=>Classical.propDecidable (a=b))=instDecidableEqFin q:=Subsingleton.elim _ _
  have hTV:T=ordinaryVortexBufferedVertices Vor 0 2:=rfl
  have hTW:
      @ordinaryVortexBufferedHubs (Fin n) (Fin q) _ _ (fun a b=>Classical.propDecidable (a=b)) P D mv β ε Vor 0 2 =
      @ordinaryVortexBufferedHubs (Fin n) (Fin q) _ _ (instDecidableEqFin q) P D mv β ε Vor 0 2 :=by rw [hdecQ]
  have hsharp':OrdinaryRootCoverSharpReferenceExists (P.comap fv) Gloc Floc Hloc I T B W 3 k (by omega)
      cover (max (18*aLoad*Fintype.card (markedVortexVertexType Vor 0)+3*((W.card:ℝ)+T.card))
        (3*aLoad*Fintype.card (markedVortexVertexType Vor 0)*3+(T.card:ℝ)*3))
      bin bin deep loss α (ρ₀/16) (βparent/2) βout (cParent*(1-δparent)^2)
      (Bhost/((ρ₀/16)*pstar^(2*3-1))) (2*hParent-ζparent) (δparent/2) (εparent+gapParent)
      ((εparent+gapParent)+geomGap) (cLinear*τ) ξreserve ζout pp εout
      (deep+2*cover) (bin+deep+4*cover) (bin+deep+loss):=by
    rw [←hηpack]
    refine ⟨?_,?_⟩
    · convert Root using 1 <;> congr! 10 <;> try rfl <;> try simp
      all_goals try norm_num
      all_goals first | (simpa using congrArg (fun S=>((Finset.card S):ℝ)) hTV) | (simpa using congrArg (fun S=>((Finset.card S):ℝ)) hTV.symm) | exact congrArg Finset.card hTV | exact congrArg Finset.card hTV.symm | exact congrArg Finset.card hTW | exact congrArg Finset.card hTW.symm | (try exact Subsingleton.elim _ _)
    · convert hsharp using 1 <;> congr! 10 <;> try rfl <;> try simp
      all_goals try norm_num
      all_goals first | (simpa using congrArg (fun S=>((Finset.card S):ℝ)) hTV) | (simpa using congrArg (fun S=>((Finset.card S):ℝ)) hTV.symm) | exact congrArg Finset.card hTV | exact congrArg Finset.card hTV.symm | exact congrArg Finset.card hTW | exact congrArg Finset.card hTW.symm | (try exact Subsingleton.elim _ _)
  have hc:=ordinary_triangle_initial_local_sharp_inputs P Gstart Bad Hstart D mv β ε Vor
    hhost
    (by intro v;convert hbal v using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    ρ d k (fun u=>sp (gu u)) false rawLocal
    α (ρ₀/16) βout (cParent*(1-δparent)^2) (Bhost/((ρ₀/16)*pstar^(2*3-1)))
    hpack (δparent/2) ((εparent+gapParent)+geomGap) cLinear pp τ εout b Bweight ηHub
    pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L ζcert rateParent βe βh
    ξroot aLoad lamGeo ellCap finishCap βeGeo βhGeo bin bin deep loss (βparent/2) (2*hParent-ζparent)
    (εparent+gapParent) ξreserve ζout (deep+2*cover) (bin+deep+4*cover) (bin+deep+loss)
    hζ hζrate hL
    (by convert profile using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hub using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hroot using 1 <;> congr! 10 <;> first | rfl | exact congrArg Finset.card hTW | exact congrArg Finset.card hTW.symm | exact Subsingleton.elim _ _)
    hlam1 hξroot haLoad hlam hellCap hfinishCap hell hξfinish
    (by convert hsharp' using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hpackcut hβeGeo
    (by convert hT using 1 <;> congr! 10 <;> first | rfl | exact congrArg Finset.card hTV | exact congrArg Finset.card hTV.symm | exact Subsingleton.elim _ _)
    (by convert hW using 1 <;> congr! 10 <;> first | rfl | exact congrArg Finset.card hTW | exact congrArg Finset.card hTW.symm | exact Subsingleton.elim _ _)
  convert hc using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
end Oberwolfach
