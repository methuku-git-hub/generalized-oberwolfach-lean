module

public import Oberwolfach.OrdinaryActualTriangleLaterPackageFromSample
public import Oberwolfach.OrdinaryTrackedLaterSameSampleHistoryInputs
public import Oberwolfach.OrdinaryTriangleSelectedSampleLevelDataGeneral
public import Oberwolfach.OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold

@[expose] public section
/-! On one matched sample, the selected common level data and every later
protected history provide the actual local sharp package. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 90000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_later_triangle_packages_from_sample
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
    (weight:∀i,OrdinaryCycle (P.comap (markedVortexVertexEmbedding Vor i)) 3→ℝ):
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
    ∀i,i+1<Vor.length→∀A (G:SimpleGraph (Fin n)) (Hs:Fin n→Fin q→Prop),
    OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Z W cost deepCost 3 (i+1) Vor.length A
      (fun t=>Vor.extendedVertices (t+2)) (fun t=>Vor.extendedVertices (t+1)) (fun t=>Vor.extendedIndices (t+2))
      (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
    ordinaryHostResources G Hs=A→G≤Q→(∀v u,Hs v u→H v u)→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→(∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    let fv:=markedVortexVertexEmbedding Vor (i+1);let gu:=markedVortexHubEmbedding Vor (i+1);
    let I:=markedVortexInnerVertices Vor (i+1);let Tloc:=ordinaryVortexBufferedVertices Vor (i+1) 2;
    let B:=markedVortexInnerHubs Vor (i+1);let Wloc:=ordinaryVortexBufferedHubs Vor (i+1) 2;
    OrdinaryTriangleLocalSharpPackage (P.comap fv) (G.comap fv) (Bad.comap fv) (fun v u=>Hs (fv v) (gu u)) I Tloc B Wloc
      (markedVortexPermutation Vor π hπ (i+1)) d k (by omega) (fun u=>sp (gu u)) false (ordinaryRawRestrictPair fv gu raw)
      α (ρ₀/16) βout (cParent*(1-δparent)^2) (Bhost/((ρ₀/16)*pstar^(2*3-1))) hpack (δparent/2)
      ((εparent+gapParent)+geomGap) cLinear p τ εout bHub BHub ηHub pR pH (θhost+α-β/2)
      (εR*I.card) (εH*B.card) βeParent βhParent ξroot aLoad ellCap cap βeGeo βhGeo lamInner ε :=by
  intro raw Bad Reference Href Q H Gstart Hstart X T Z W cost deepCost hw hf hlevels i hi A G Hs hhist hstate hG hH hbal hdiv fv gu I Tloc B Wloc
  have hhistInputs:=ordinary_tracked_later_same_sample_history_inputs (mAbs:=mAbs) (t:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
    P Target G Hs π d σx Fs Comps embed D mv β ε Vor
    Kres Ares Wterm Bterm ξabs editCost JQ JH rate ξroot hrate hξroot hSP i Vor.length A
    (by convert hw using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hf using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hhist using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _) hstate
  obtain ⟨hPairRim,hPairSpoke,havoid,htrace,hcost,hhost⟩:=hhistInputs
  have hg:=hgeometry (Fin n) (Fin q) P D mv hreg hn hhalf hρlo hρhi hmGeo Vor i hi
  obtain ⟨hrootGeo,hT,hW,hdeep,_hbin,_hcin,hstatic,hscaleV,hscaleU⟩:=hg
  have hsize:(Tloc.card:ℝ)+Wloc.card≤lamRoot*Fintype.card (markedVortexVertexType Vor (i+1)):=
    hrootGeo.trans (mul_le_mul_of_nonneg_right hlamRoot (by positivity))
  have hgeneral:=ordinary_triangle_selected_sample_level_general_of_fin n q D mv k d β ε P Vor π hπ
    α ρ₀ pstar βP ηP ηH βH cParent Bhost εTri δparent hParent pR pH pstar κ aLoad εR εH
    bHub BHub ηHub capHub βeParent βhParent (fun _=>θhost+α-β/2)
    (fun t=>εR*(markedVortexInnerVertices Vor t).card) (fun t=>εH*(markedVortexInnerHubs Vor t).card)
    sp false raw coins (i+1) (weight (i+1))
    (by convert hlevels (i+1) hi using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
  have hQ:Q≤P:=sdiff_le.trans hSP
  have hρpos:0< initialIndexDensity (Fin q) D:=hρ.trans_le hρlo
  have hpkg:=ordinary_actual_triangle_later_package_from_sample d ρ₀ pstar pstar href δcut ζcut εcut ζlimit εsample
    ε ξroot aLoad κ β ηbal ηProfile α ζ cBoundary δDeep rate 0 rateParent mBalance mCover mInitial ηInitial δInitial
    hInitialAt hbalance hcover hζlim hζrate hζcut hεcut hζlimit
    (Fin n) (Fin q) Bool Bool P Q G H Hs D mv hQ hreg hn hhalf hρlo hρhi hmB hmC
    Vor π hπ raw coins false sp Kres cost deepCost i hi A pR pH θhost εR εH βeParent βhParent (min (α/4) (1/4:ℝ)) pstar
    ηHub bHub BHub capHub hζcap hpR hpR1 hpH hpH1 hθhost hdegree hpEq hsp hεR0 hεR hεRsample hεH0 hεH hεHsample
    hβe0 hβecap hβh0 hβhcap hPairRim
    (by convert hPairSpoke using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert havoid using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert htrace using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hstate using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    Vor.length (by omega) hρpos hβ0 hβ1 hε hmv
    (fun _ _=>0) (fun _ _=>0)
    (by convert hhist using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by simpa using hcost) hmI hεRinitial hεHinitial hηInitial hbal hdiv hpHpos hcut hhref
    k hk βH ηH Bhost βparent εparent ζparent gapParent lamRoot hParent δparent cParent N₀
    hBhost hρ hpstar hζparent hN₀ hscale hroot (hlevelsize (i+1) hi) βP ηP εTri (weight (i+1)) rfl rfl
    (by convert hgeneral using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hpR hpH hcParent
    hsize hξ haLoad hηbal hdeep (ρ₀/16) βout ((εparent+gapParent)+geomGap) ηpack ξreserve ζout p εout lamGeo ellCap cap βeGeo βhGeo hpack cLinear τ lamInner
    (by convert hstatic using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hscaleV using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hscaleU using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hRate0 hhost hlam hlam1 hrootGeo hellCap hcap hell hξcap hpackcut hβeGeo hT hW hηpack hRateInner
  convert hpkg using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
end Oberwolfach
