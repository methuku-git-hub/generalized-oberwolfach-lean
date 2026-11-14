module

public import Oberwolfach.OrdinaryTrackedLaterTrianglePackagesFromSample
public import Oberwolfach.OrdinaryTriangleTrackedSplitFromSameSamplePackages

@[expose] public section
/-! The same sample and matching provide every later package; together with
its initial package and common level events this yields the split certificates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 90000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_tracked_split_with_later_from_sample
    {n q mAbs tAbs aAbs bAbs:ℕ} (d k:ℕ) (hk:4≤k)
    (ρ₀ pstar href δcut ζcut εcut ζlimit εsample:ℝ)
    (ε ξroot aLoad κ β ηbal ηProfile α ζ cBoundary δDeep rate rateParent:ℝ)
    (mBalance mCover mInitial:ℕ) (ηInitial δInitial:ℝ)
    (hInitialAt:OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pstar pstar ηInitial cBoundary δInitial d β mInitial)
    (hbalance:OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pstar pstar ηProfile ζ cBoundary δDeep rate d 2 β 0 mBalance)
    (hcover:OrdinaryActualTraceTriangleFineCoverAtLocalBalance 2 ρ₀ pstar href δcut ζcut εcut ζlimit εsample ε ξroot aLoad κ β ηbal d mCover)
    (hζlim:ζ≤ζlimit) (hζrate:ζ≤rateParent) (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit)
    (P Target:SimpleGraph (Fin n)) (D mv:ℕ) (Vor:Vortex (Fin q) P D β ε mv)
    (π:Equiv.Perm (Fin n)) (hπ:∀i x,π x∈Vor.extendedVertices i↔x∈Vor.extendedVertices i)
    (σx:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (coins:Sym2 (Fin n)→Bool) (sp:Fin q→Bool→ℝ)
    (Fs:Fin q→SimpleGraph (Fin n)) (Comps:∀u,Finset (Fs u).ConnectedComponent)
    (embed:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉Comps u}↪Fin n)
    (Kres:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (Ares Wterm:Finset (Fin n)) (Bterm:Finset (Fin q))
    (ξabs editCost:ℝ) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (pR pH θhost εR εH bHub BHub ηHub capHub βeParent βhParent:ℝ)
    (βP ηP ηH βH cParent Bhost εTri βparent δparent hParent εparent gapParent ζparent lamRoot:ℝ) (N₀:ℕ)
    (βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap:ℝ) (mGeom:ℕ)
    (hpack cLinear τ ellCap cap lamInner:ℝ)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card (Fin n)) (hhalf:(Fintype.card (Fin n):ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity (Fin q) D) (hρhi:initialIndexDensity (Fin q) D≤1)
    (hSP:Target≤P) (hmB:mBalance≤mv) (hmC:mCover≤mv) (hmI:mInitial≤mv) (hmGeo:mGeom≤mv)
    (hβ0:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hmv:0<mv) (hrate:0≤rate) (hξroot:0≤ξroot)
    (hζcap:ζ≤capHub) (hpR:pstar≤pR) (hpR1:pR≤1) (hpH:pstar≤pH) (hpH1:pH≤1)
    (hθhost:1/2≤θhost) (hdegree:(θhost+α)*Fintype.card (Fin n)≤D)
    (hpEq:pR=initialIndexDensity (Fin q) D*pH) (hsp:∀u,sp u false=pH)
    (hεR0:0≤εR) (hεR:εR≤δDeep) (hεRsample:εR≤εsample)
    (hεH0:0≤εH) (hεH:εH≤δDeep) (hεHsample:εH≤εsample)
    (hβe0:0≤βeParent) (hβecap:βeParent≤cBoundary*ε) (hβh0:0≤βhParent) (hβhcap:βhParent≤cBoundary*ε)
    (hεRinitial:εR≤δInitial) (hεHinitial:εH≤δInitial) (hηInitial:ηInitial≤ηbal)
    (hpHpos:0<pH) (hcut:δcut≤min ((min (α/4) (1/4:ℝ))/32) (pstar/512))
    (hhref:href≤(min (α/4) (1/4:ℝ))*pstar/64)
    (hBhost:0≤Bhost) (hpstar:0<pstar) (hζparent:0≤ζparent) (hN₀:1≤N₀)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH Bhost (ρ₀/16) pstar βparent εparent ζparent rateParent N₀)
    (hroot:OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad 2 k 0 (by omega) α βparent cParent
      (Bhost/((ρ₀/16)*pstar^(2*3-1))) (2*hParent-ζparent) δparent εparent (ρ₀/16) gapParent lamRoot)
    (hξ:0≤ξroot) (haLoad:0≤aLoad) (hηbal:0≤ηbal) (hcParent:0≤cParent)
    (hlam:0≤lamGeo) (hlam1:lamGeo≤1/4) (hlamRoot:lamGeo≤lamRoot)
    (hgeometry:OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold 2 0 d k mGeom β ε ρ₀ lamGeo ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βeGeo βhGeo pH εR εH
      (βparent/2) (cParent*(1-δparent)^2) (Bhost/((ρ₀/16)*pstar^(2*3-1)))
      (εparent+gapParent) geomGap βout ζout ηpack εout)
    (hlevelsize:∀i,i<Vor.length→N₀≤Fintype.card (markedVortexVertexType Vor i))
    (hRate0:0≤rateParent) (hRateInner:rateParent≤lamInner*ε/4)
    (hellCap:0≤ellCap) (hcap:0≤cap) (hell:max (18*aLoad+3*lamGeo) ((3*aLoad+lamGeo)*3)≤ellCap)
    (hξcap:10*ξroot≤cap) (hpackcut:hpack≤(2*hParent-ζparent)-ξreserve-ζout)
    (hβeGeo:0≤βeGeo) (hηpack:ηpack=cLinear*τ)
    (weight:∀i,OrdinaryCycle (P.comap (markedVortexVertexEmbedding Vor i)) 3→ℝ)
    (εrows tpot ν:ℝ) (M v₀:ℕ)
    (hcert:OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pstar εrows tpot lamInner d k
      (ρ₀/16) βout (cParent*(1-δparent)^2) (Bhost/((ρ₀/16)*pstar^(2*3-1))) hpack (δparent/2)
      ((εparent+gapParent)+geomGap) cLinear bHub BHub ηHub p βeGeo βhGeo ν cap τ εout ellCap M v₀)
    (hv:v₀≤mv) (hterminal:(M:ℝ)≤ε*mv/2) (hθcycle:cycleThreshold 3≤θhost)
    (hRrows:2*εR≤εrows) (hHrows:2*εH≤εrows)
    (hbudgetE:βeGeo+3*max cap ellCap≤βeParent) (hbudgetH:βhGeo+2*ellCap≤βhParent)
    (hfinish:ν+cap+4*p≤rate)
    (endpointWeight:∀i,markedVortexVertexType Vor i→Sym2 (markedVortexVertexType Vor i⊕markedVortexHubType Vor i)→ℝ):
    letI : DecidableEq (Fin n):=Classical.decEq _
    letI : DecidableEq (Fin q):=Classical.decEq _
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σx e);
    let Bad:=permutationConflictGraph π (3*d);
    let Reference:=rawWheelGraph P raw\Bad;let Href:=rawWheelSpokes π d raw false;
    let Q:=Target\ordinaryEmbeddedComplements Fs Comps embed;let H:=fun v u=>v∉Set.range (embed u);
    let Gstart:=Q\ordinaryResourceRim Q Kres;let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kres);
    let X:=fun t=>Vor.extendedVertices (t+1);let T:=fun t=>Vor.extendedVertices (t+2);
    let Z:=fun t=>Vor.extendedIndices (t+1);let W:=fun t=>Vor.extendedIndices (t+2);
    let cost:=ordinaryVortexSelectedCost Vor rate;let deepCost:=ordinaryFineDeepCost Vor ξroot;
    OrdinaryCorrectedProtectedReservoirWitness 3 mAbs tAbs aAbs bAbs ξabs Reference Bad Href Ares
      (Vor.extendedVertices 1) Wterm Bterm (Vor.extendedIndices 1) Kres JQ JH→
    OrdinaryTrackedComplementFor P Target π d σx Fs Comps (Vor.extendedVertices 1) (Vor.extendedIndices 1) Kres editCost embed→
    (∀i,i<Vor.length→OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Vor π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bhost εTri δparent hParent pR pH pstar κ aLoad εR εH
      bHub BHub ηHub capHub βeParent βhParent (fun _=>θhost+α-β/2)
      (fun t=>εR*(markedVortexInnerVertices Vor t).card) (fun t=>εH*(markedVortexInnerHubs Vor t).card)
      sp false raw coins i (weight i))→
    (∀i,i<Vor.length→EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Vor i))
      (markedVortexInnerVertices Vor i) (markedVortexInnerVertices Vor i)ᶜ (endpointWeight i))→
    (∀i,i<Vor.length→EndpointPhysicalPotentialEvent (P.comap (markedVortexVertexEmbedding Vor i))
      (Bad.comap (markedVortexVertexEmbedding Vor i)) (markedVortexInnerVertices Vor i) (markedVortexInnerHubs Vor i)
      (markedVortexInnerVertices Vor i)ᶜ (markedVortexPermutation Vor π hπ i) d false (endpointWeight i) pR pH tpot
      (ordinaryRawRestrictPair (markedVortexVertexEmbedding Vor i) (markedVortexHubEmbedding Vor i) raw))→
    (let fv:=markedVortexVertexEmbedding Vor 0;let gu:=markedVortexHubEmbedding Vor 0;
      let I:=markedVortexInnerVertices Vor 0;let Tloc:=ordinaryVortexBufferedVertices Vor 0 2;
      let B:=markedVortexInnerHubs Vor 0;let Wloc:=ordinaryVortexBufferedHubs Vor 0 2;
      OrdinaryTriangleLocalSharpPackage (P.comap fv) (Gstart.comap fv) (Bad.comap fv) (fun v u=>Hstart (fv v) (gu u)) I Tloc B Wloc
        (markedVortexPermutation Vor π hπ 0) d k (by omega) (fun u=>sp (gu u)) false (ordinaryRawRestrictPair fv gu raw)
        α (ρ₀/16) βout (cParent*(1-δparent)^2) (Bhost/((ρ₀/16)*pstar^(2*3-1))) hpack (δparent/2)
        ((εparent+gapParent)+geomGap) cLinear p τ εout bHub BHub ηHub pR pH (θhost+α-β/2)
        (εR*I.card) (εH*B.card) βeParent βhParent ξroot aLoad ellCap cap βeGeo βhGeo lamInner ε)→
    OrdinaryTrackedSplitWheelCertificatesAt P Target Bad Fs Comps 3 Kres D mv β ε Vor Vor.length cost deepCost embed :=by
  intro raw Bad Reference Href Q H Gstart Hstart X T Z W cost deepCost hw hf hlevels hparents hevents hinit
  have hlater:=ordinary_tracked_later_triangle_packages_from_sample (mAbs:=mAbs) (tAbs:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
    d k hk ρ₀ pstar href δcut ζcut εcut ζlimit εsample ε ξroot aLoad κ β ηbal ηProfile α ζ cBoundary δDeep rate rateParent
    mBalance mCover mInitial ηInitial δInitial hInitialAt hbalance hcover hζlim hζrate hζcut hεcut hζlimit
    P Target D mv Vor π hπ σx coins sp Fs Comps embed Kres Ares Wterm Bterm ξabs editCost JQ JH
    pR pH θhost εR εH bHub BHub ηHub capHub βeParent βhParent
    βP ηP ηH βH cParent Bhost εTri βparent δparent hParent εparent gapParent ζparent lamRoot N₀
    βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap mGeom hpack cLinear τ ellCap cap lamInner
    hreg hn hhalf hρ hρlo hρhi hSP hmB hmC hmI hmGeo hβ0 hβ1 hε hmv hrate hξroot
    hζcap hpR hpR1 hpH hpH1 hθhost hdegree hpEq hsp hεR0 hεR hεRsample hεH0 hεH hεHsample
    hβe0 hβecap hβh0 hβhcap hεRinitial hεHinitial hηInitial hpHpos hcut hhref
    hBhost hpstar hζparent hN₀ hscale hroot hξ haLoad hηbal hcParent hlam hlam1 hlamRoot hgeometry
    hlevelsize hRate0 hRateInner hellCap hcap hell hξcap hpackcut hβeGeo hηpack weight hw hf hlevels
  have hh:=ordinary_triangle_tracked_split_from_same_sample_packages β ε ρ₀ α pstar εrows tpot lamInner d k
    (ρ₀/16) βout (cParent*(1-δparent)^2) (Bhost/((ρ₀/16)*pstar^(2*3-1))) hpack (δparent/2)
    ((εparent+gapParent)+geomGap) cLinear bHub BHub ηHub p βeGeo βhGeo ν cap τ εout ellCap M v₀ hcert
    P Target D mv Vor π hπ Fs Comps embed Kres σx coins sp θhost pR pH εR εH βeParent βhParent rate ξroot
    hreg (by simpa using hn) (by simpa using hhalf) hρlo hρhi hv hterminal hθcycle (by simpa using hdegree)
    hpR hpR1 hpH hpH1 hpEq hεR0 hRrows hεH0 hHrows hbudgetE hbudgetH hfinish
    pstar βP ηP ηH βH cParent Bhost εTri δparent hParent κ aLoad bHub BHub ηHub capHub βeParent βhParent
    weight endpointWeight
    (by convert hlevels using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hparents using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hevents using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by dsimp only at hinit ⊢; convert hinit using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by
      intro i hi A G Hs hhist hstate hG hH hbal hdiv
      have hpkg:=hlater i hi A G Hs
        (by convert hhist using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
        (by convert hstate using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
        (by convert hG using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
        (by convert hH using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
        (by convert hbal using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
        (by convert hdiv using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
      dsimp only at hpkg ⊢
      convert hpkg using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
  convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
