module

public import Oberwolfach.OrdinaryTrackedSelectedHistoryCertificate
public import Oberwolfach.OrdinaryWheelSelectedSampleLevelData

@[expose] public section
/-! The later tracked wheel certificate consumes the level package obtained
from the common parent and deep event on the very same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

theorem ordinary_tracked_history_from_sample_level
    (mWheel loadK d:ℕ) (hmWheel:3≤mWheel) (ρ₀ pmin hmin href δcut ζcut εcut ζlimit εsample:ℝ)
    (ε ξ aLoad a ρ θ β η ηProfile α ζ cBoundary δ rate C rateParent:ℝ) (mBalance mCover mInitial:ℕ) (ηInitial δInitial:ℝ)
    (hrate:0≤rate) (hC:0≤C)
    (hInitialAt:OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial)
    (hbalance:OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δ rate d 2 β C mBalance)
    (hcover:OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad a ρ θ β η d mCover)
    (hζlim:ζ≤ζlimit) (hζrate:ζ≤rateParent)
    (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit):
    ∀(n q:ℕ) (P Target G:SimpleGraph (Fin n)) (Hs:Fin n→Fin q→Prop) (D m:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card (Fin n)→(Fintype.card (Fin n):ℝ)/2≤D→
      ρ₀≤ initialIndexDensity (Fin q) D→initialIndexDensity (Fin q) D≤1→mBalance≤m→mCover≤m→
    ∀(Q:Vortex (Fin q) P D β ε m) (π:Equiv.Perm (Fin n))
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σx:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
      (coins:Sym2 (Fin n)→Bool) (s:Fin q→Bool→ℝ)
      (Kres:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (i:ℕ),i+1<Q.length→
    ∀(Fs:Fin q→SimpleGraph (Fin n)) (Comps:∀u,Finset (Fs u).ConnectedComponent)
      (embed:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉Comps u}↪Fin n)
      (mAbs tAbs aAbs bAbs:ℕ) (Ares Wterm:Finset (Fin n)) (Bterm:Finset (Fin q))
      (ξabs editCost:ℝ) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop),
    let σ:=fun e=>expandedOrdinarySelectedCollapse e (σx e)
    let j:=false
    let Gbase:=Target\ordinaryEmbeddedComplements Fs Comps embed
    let Hbase:=fun v u=>v∉Set.range (embed u)
    let cost:=ordinaryVortexSelectedCost Q rate;
    ∀(A:Finset (Sym2 (Fin n)⊕((Fin n)×(Fin q)))) (pR pH θhost εR εH βe βh αcut pstar:ℝ),
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1)
    let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) 2
    let B:=markedVortexInnerHubs Q (i+1);let W:=ordinaryVortexBufferedHubs Q (i+1) 2
    let ρi:=markedVortexPermutation Q π hπ (i+1)
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u)
    let raw:=ordinaryRawRestrictPair f g σ
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j
    let S:=Gbase;let H:=Hbase
    let S₀:=S\ordinaryResourceRim S Kres;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kres)
    let X:=fun k=>Q.extendedVertices (k+1);let Tdeep:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let Wdeep:=fun k=>Q.extendedIndices (k+2)
    let Jwin:=Finset.Icc (i+2-2) i
    let Ledit:=2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j;
    ∀(ηf bPair Bweight capHub:ℝ),ζ≤capHub→
    pmin≤pR→pR≤1→hmin≤pH→pH≤1→1/2≤θhost→(θhost+α)*Fintype.card (Fin n)≤D→
    pR=initialIndexDensity (Fin q) D*pH→(∀u,s u j=pH)→
    0≤εR→εR≤δ→εR≤εsample→0≤εH→εH≤δ→εH≤εsample→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
    OrdinaryCorrectedProtectedReservoirWitness (mWheel+1) mAbs tAbs aAbs bAbs ξabs (R\F) F J
      Ares (Q.extendedVertices 1) Wterm Bterm (Q.extendedIndices 1) Kres JQ JH→
    OrdinaryTrackedComplementFor P Target π d σx Fs Comps (Q.extendedVertices 1) (Q.extendedIndices 1) Kres editCost embed→
    ordinaryHostResources G Hs=A→
    ∀L:ℕ, i<L→(0< initialIndexDensity (Fin q) D)→0≤β→β≤1/4→0<ε→0<m→
    OrdinaryUniformProtectedBalanceHistory S₀ H₀ X Tdeep Z Wdeep cost (ordinaryFineDeepCost Q ξ) (mWheel+1) (i+1) L A
      (fun t=>Q.extendedVertices (t+2)) (fun t=>Q.extendedVertices (t+1))
      (fun t=>Q.extendedIndices (t+2)) (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
    mInitial≤m→εR≤δInitial→εH≤δInitial→ηInitial≤η→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    0<pH→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    ∀(k:ℕ) (hk:4≤k) (βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight:ℝ) (N₀:ℕ),
    0≤B0→0<ρ₀→0<pstar→0≤ζparent→1≤N₀→
    OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH B0 (ρ₀/16) pstar βparent εparent ζparent rateParent N₀→
    OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad mWheel k loadK (Nat.le_trans (Nat.le_succ 2) hmWheel) α βparent cweight
      (B0/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*hRef-ζparent) δparent εparent (ρ₀/16) gap lam→
    N₀≤Fintype.card (markedVortexVertexType Q (i+1))→
    ∀(βP ηP row εTri:ℝ) (weight:OrdinaryCycle Ploc (mWheel+1)→ℝ),
    pstar≤pR→pstar≤pH→0≤cweight→
    ∀(eSample hSample CSample:ℝ),pmin=pstar→βe=eSample*ε→βh=hSample*ε→
    Bweight=4*CSample/pmin^(3*mWheel+1)→
    OrdinaryWheelSelectedSampleLevelData n q D m mWheel loadK k d hmWheel β ε P Q π hπ
      α ρ₀ pstar βP ηP row ηH βH cweight B0 εTri δparent hRef
      pR pH pmin αcut bPair CSample ηf a aLoad ρ θ capHub eSample hSample εR εH
      (fun _=>θhost+α-β/2) (fun t=>εR*(markedVortexInnerVertices Q t).card)
      (fun t=>εH*(markedVortexInnerHubs Q t).card) s j σ coins (i+1) weight→
    0≤ξ→0≤aLoad→0≤η→
    letI : DecidableEq (markedVortexVertexType Q (i+1)):=Classical.decEq _
    letI : DecidableEq (markedVortexHubType Q (i+1)):=Classical.decEq _
    let bin:=η*I.card;let cin:=ηInitial*I.card+2*(ordinaryFineDeepCost Q ξ) i;
    let deep:ℝ:=(initialIndexDensity (Fin q) D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+
      3*(2*((3*d:ℕ):ℝ))+2*(ordinaryFineDeepCost Q ξ) i;
    ∀(βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap:ℝ) (mGeom:ℕ),
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q (i+1))+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q (i+1))*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    let cover:=10*ξ*I.card;let loss:=12*aLoad*Fintype.card (markedVortexVertexType Q (i+1));
    let fout:=deep+2*cover;let binner:=bin+deep+4*cover;let crossout:=cin+deep+loss;
    let Aroot:=Finset.univ\T;let Croot:=Finset.univ\W;
    let Xf:Finset Aroot:=Finset.univ.filter (fun v=>v.val∈I);
    let Zf:Finset Croot:=Finset.univ.filter (fun u=>u.val∈B);
    mGeom≤m→lamGeo≤lam→
    OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold mWheel loadK d k mGeom β ε ρ₀ lamGeo ξreserve ξ aLoad η ηInitial γgeom edit p βeGeo βhGeo pH εR εH
      (βparent/2) (cweight*(1-δparent)^mWheel) (B0/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (εparent+gap) geomGap βout ζout ηpack εout→
    ∀(Ncert N:ℕ),Ncert≤N→2/ε≤N→(N:ℝ)≤ε*m/2→
    ∀(δend ζh ζe γ eCoeff:ℝ),0≤δend→εR≤δend/4→εH≤δend/4→
      rateParent≤δend*ε/8→0≤rateParent→0<ζh→0<ζe→0<γ→γ≤eCoeff→0≤lamGeo→lamGeo≤1/4→
    ∀(cert:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad cert),
    cert.m=mWheel→cert.k=k→cert.loadK=loadK→cert.α=α→cert.ω=ρ₀/16→cert.β=βout→
    cert.bRoot=cweight*(1-δparent)^mWheel→cert.BRoot=B0/((ρ₀/16)*pstar^(2*(mWheel+1)-1))→
    cert.δ=δparent/2→cert.εstar=(εparent+gap)+geomGap→cert.ηpack=ηpack→cert.p=p→cert.εgeom=εout→
    cert.βe=βeGeo→cert.βh=βhGeo→cert.bHub=bPair→cert.BHub=Bweight→cert.ηhub=ηf→
    cert.Ncert=Ncert→cert.δend=δend→cert.ζhub=ζh→cert.ζlocal=ζe→cert.γ=γ→
    ∀hParentRate:ℝ,βe=eCoeff*ε→βh=hParentRate*ε→
    (2*(3*d):ℕ)≤cert.b₀→(2*((3*d:ℕ):ℝ))≤cert.L→
    cert.hpack≤(2*hRef-ζparent)-ξreserve-ζout→cert.κ≤ρ₀/8→cert.p₀≤pR→cert.p₀≤pH→
    ∀(Nfinish M:ℕ) (rateFinish θmatch ellCap finishCap kcap:ℝ),0<θmatch→
    θmatch≤(min (cert.ζhub*cert.γ*(1/4:ℝ)) (cert.ζlocal*(1/4:ℝ))/2)*ε→
    cert.εsup≤cert.p^2/4→cert.p≤4*θmatch→20*Real.sqrt (2*cert.p)≤θmatch/2→
    max (max (max (4*cert.n₀) (4*cert.Nreserve)) (max cert.Nclean 64)) (max cert.Ncert Nfinish)≤M→
    M≤I.card→max (18*aLoad+3*(((cert.loadK:ℝ)+1)*lamGeo)) ((3*aLoad+lamGeo)*((cert.m:ℝ)+1))≤ellCap→
    10*ξ≤finishCap→cert.L≤kcap^2*M→
    OrdinaryAsymmetricFinishSchedule cert.m Nfinish eCoeff hParentRate ε cert.βe cert.βh θmatch cert.p cert.δsample ellCap finishCap kcap rateFinish cert.ν cert.cap→
    OrdinaryWheelLikelySeparateCostsCertificate Gloc Floc Hloc I T B W (mWheel+1)
      (rateFinish*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))) cover :=by
  intro n q P Target G Hs D m hreg hn hD hρlo hρhi hmB hmC Q π hπ σx coins s Kres i hi
    Fs Comps embed mAbs tAbs aAbs bAbs Ares Wterm Bterm ξabs editCost JQ JH σ j Gbase Hbase cost
    A pR pH θhost εR εH βe βh αcut pstar f g I T B W ρi Ploc Floc Gloc Hloc raw F R J S H S₀ H₀ X Tdeep Z Wdeep Jwin Ledit
    ηf bPair Bweight capHub hζcap
    hpRlo hpRhi hpHlo hpHhi hθhost hdegree hpEq hs hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβe hβh0 hβh hw hf hstate
    L hiL hρpos hβ0 hβ1 hεpos hm0 huniform hmI hεRinitial hεHinitial hηInitial hbal hdiv hpH hcut hhref
    k hk βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale hroot hN
    βP ηP row εTri weight hpRstar hpHstar hcweight eSample hSample CSample hpmin heSample hhSample hBweight hsample hξ0 haLoad0 hη0
    bin cin deep βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap mGeom ell cover loss fout binner crossout Aroot Croot Xf Zf
    hmGeom hlamGeom hgeometry Ncert N hNcert hNsize hterminal δend ζh ζe γ eCoeff hδend hRend hHend hRateEnd hRate0 hζh hζe hγ hCoeff hlam0 hlam1
    cert hcert hs_m hs_k hs_load hs_α hs_ω hs_β hs_bRoot hs_BRoot hs_δ hs_εstar hs_ηpack hs_p hs_εgeom
    hs_βe hs_βh hs_bHub hs_BHub hs_ηhub hs_Ncert hs_δend hs_ζhub hs_ζlocal hs_γ
    hParentRate hβeEq hβhEq hb₀ hLconf hpack hκ hp₀R hp₀H Nfinish M rateFinish θmatch ellCap finishCap kcap
    hθmatch hθcap hεsup hpθ hsqrt hbase hM hell hcoverCap hbudget hsched
  dsimp only [OrdinaryWheelSelectedSampleLevelData] at hsample
  obtain ⟨hfamily,hdeep,hgood,hgood2,hrim,heventParent,hcutsParent,hinputs,hweight⟩:=hsample
  rw [←heSample,←hhSample,←hBweight] at hfamily
  rw [hpmin] at hrim
  exact ordinary_tracked_selected_history_certificate mWheel loadK d hmWheel ρ₀ pmin hmin href δcut ζcut εcut ζlimit εsample
    ε ξ aLoad a ρ θ β η ηProfile α ζ cBoundary δ rate C rateParent mBalance mCover mInitial ηInitial δInitial
    hrate hC hInitialAt hbalance hcover hζlim hζrate hζcut hεcut hζlimit
    n q P Target G Hs D m hreg hn hD hρlo hρhi hmB hmC Q π hπ σx coins s Kres i hi
    Fs Comps embed mAbs tAbs aAbs bAbs Ares Wterm Bterm ξabs editCost JQ JH
    A pR pH θhost εR εH βe βh αcut pstar ηf bPair Bweight capHub hζcap (by convert hfamily using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hpRlo hpRhi hpHlo hpHhi hθhost hdegree hpEq hs hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβe hβh0 hβh hw hf (by convert hgood using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _) hstate
    L hiL hρpos hβ0 hβ1 hεpos hm0 (by convert hgood2 using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _) huniform hmI hεRinitial hεHinitial hηInitial hbal hdiv (by convert hdeep using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _) (by convert hrim using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _) hpH hcut hhref
    k hk βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale hroot hN
    βP ηP row εTri weight (by convert hinputs using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _) hpRstar hpHstar hcweight (by convert hweight using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _) (by convert heventParent using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _) (by convert hcutsParent using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _) hξ0 haLoad0 hη0
    βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap mGeom hmGeom hlamGeom hgeometry Ncert N hNcert hNsize hterminal
    δend ζh ζe γ eCoeff hδend hRend hHend hRateEnd hRate0 hζh hζe hγ hCoeff hlam0 hlam1
    cert hcert hs_m hs_k hs_load hs_α hs_ω hs_β hs_bRoot hs_BRoot hs_δ hs_εstar hs_ηpack hs_p hs_εgeom
    hs_βe hs_βh hs_bHub hs_BHub hs_ηhub hs_Ncert hs_δend hs_ζhub hs_ζlocal hs_γ
    hParentRate hβeEq hβhEq hb₀ hLconf hpack hκ hp₀R hp₀H Nfinish M rateFinish θmatch ellCap finishCap kcap
    hθmatch hθcap hεsup hpθ hsqrt hbase hM hell hcoverCap hbudget hsched
end Oberwolfach
