module

public import Oberwolfach.OrdinaryActualTraceSharpFromSelectedGeometry
public import Oberwolfach.OrdinaryProtectedTraceCertificateFromLocalData

@[expose] public section
/-! Apply the selected local certificate to the sharp data obtained on an
actual protected history of the same sampled reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_trace_certificate_from_selected_geometry
    (mWheel loadK d:ℕ) (hmWheel:3≤mWheel) (ρ₀ pmin hmin href δcut ζcut εcut ζlimit εsample:ℝ)
    (ε ξ aLoad a ρ θ β η ηProfile α ζ cBoundary δ rate C rateParent:ℝ) (mBalance mCover mInitial:ℕ) (ηInitial δInitial:ℝ)
    (hInitialAt:OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial)
    (hbalance:OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δ rate d 2 β C mBalance)
    (hcover:OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad a ρ θ β η d mCover)
    (hζlim:ζ≤ζlimit) (hζrate:ζ≤rateParent)
    (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit):
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P Gbase G:SimpleGraph V) (Hbase Hs:V→U→Prop) (D m:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→mBalance≤m→mCover≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (j:Color) (s:U→Color→ℝ)
      (Kres:Finset (Sym2 V⊕(V×U))) (cost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
    ∀(A:Finset (Sym2 V⊕(V×U))) (pR pH θhost εR εH βe βh αcut pstar:ℝ),
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
    OrdinaryUniformInnerHubEvent mWheel P D m d β ε Q π hπ pR pH βe βh bPair Bweight ηf capHub
      (fun _=>θhost+α-β/2) (fun t=>εR*(markedVortexInnerVertices Q t).card)
      (fun t=>εH*(markedVortexInnerHubs Q t).card) s j σ→
    pmin≤pR→pR≤1→hmin≤pH→pH≤1→1/2≤θhost→(θhost+α)*Fintype.card V≤D→
    pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
    0≤εR→εR≤δ→εR≤εsample→0≤εH→εH≤δ→εH≤εsample→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
    (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,(R\F).Adj v w↔Gbase.Adj v w)→
    (∀v∈Q.extendedVertices 1,∀u∈Q.extendedIndices 1,J v u↔Hbase v u)→
    Disjoint Kres (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ→
    OrdinaryProtectedTrace S₀ H₀ X Tdeep Z Wdeep cost (ordinaryFineDeepCost Q ξ) (i+1) A→ ordinaryHostResources G Hs=A→
    ∀L:ℕ, i<L→(0< initialIndexDensity U D)→0≤β→β≤1/4→0<ε→0<m→
    OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ→
    ∀inner cross:ℕ→ℕ→ℝ,
    OrdinaryUniformProtectedBalanceHistory S₀ H₀ X Tdeep Z Wdeep cost (ordinaryFineDeepCost Q ξ) (mWheel+1) (i+1) L A
      (fun t=>Q.extendedVertices (t+2)) (fun t=>Q.extendedVertices (t+1))
      (fun t=>Q.extendedIndices (t+2)) (fun t=>Finset.Icc (t+3-2) t) inner cross→
    (∀t∈Jwin,0≤cost t ∧ cost t≤4*rate*Fintype.card (markedVortexVertexType Q t⊕markedVortexHubType Q t)+C)→
    mInitial≤m→εR≤δInitial→εH≤δInitial→ηInitial≤η→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexDeepCoverEvent mWheel loadK d a aLoad ρ θ P D m β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+2)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    ∀(k:ℕ) (hk:4≤k) (βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight:ℝ) (N₀:ℕ),
    0≤B0→0<ρ₀→0<pstar→0≤ζparent→1≤N₀→
    OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH B0 (ρ₀/16) pstar βparent εparent ζparent rateParent N₀→
    OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad mWheel k loadK (by omega) α βparent cweight
      (B0/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*hRef-ζparent) δparent εparent (ρ₀/16) gap lam→
    N₀≤Fintype.card (markedVortexVertexType Q (i+1))→
    ∀(βP ηP row εTri:ℝ) (weight:OrdinaryCycle Ploc (mWheel+1)→ℝ),
    OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri Ploc Floc ρi B pR pH
      (2*(Fintype.card (markedVortexHubType Q (i+1)):ℝ)/initialIndexDensity U D) β→
    pstar≤pR→pstar≤pH→0≤cweight→
    (∀C,cweight/(Fintype.card (markedVortexVertexType Q (i+1)):ℝ)^((mWheel+1)-2)≤weight C ∧
      weight C≤B0/(Fintype.card (markedVortexVertexType Q (i+1)):ℝ)^((mWheel+1)-2))→
    ordinaryCombinedHostEvent mWheel d k hmWheel Ploc Floc ρi (max (1/2) (cycleThreshold (mWheel+1))) α pstar
      βP ηP row ηH βH cweight B0 pR pH weight (fun u=>s (g u)) j raw→
    OrdinaryTriangleReferenceNormalizedCuts Ploc Floc ρi d j δparent hRef raw
      (fun e=>coins (Sym2.map f e))→
    0≤ξ→0≤aLoad→0≤η→
    letI : DecidableEq (markedVortexVertexType Q (i+1)):=Classical.decEq _
    letI : DecidableEq (markedVortexHubType Q (i+1)):=Classical.decEq _
    let bin:=η*I.card;let cin:=ηInitial*I.card+2*(ordinaryFineDeepCost Q ξ) i;
    let deep:ℝ:=(initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+
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
  intro V U Γ Color _ _ _ _ _ _ P Gbase G Hbase Hs D m hreg hn hD hρlo hρhi hmB hmC Q π hπ σ coins j s Kres cost i hi
    A pR pH θhost εR εH βe βh αcut pstar f g I T B W ρi Ploc Floc Gloc Hloc raw F R J S H S₀ H₀ X Tdeep Z Wdeep Jwin Ledit
    ηf bPair Bweight capHub hζcap hfamily
    hpRlo hpRhi hpHlo hpHhi hθhost hdegree hpEq hs hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβe hβh0 hβh hPairRim hPairSpoke havoid hgood htrace hstate L hiL hρpos hβ0 hβ1 hεpos hm0 hgood2 inner cross huniform hcost hmI hεRinitial hεHinitial hηInitial hbal hdiv hdeep hrim hpH hcut hhref
    k hk βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale hroot hN
    βP ηP row εTri weight hinputs hpRstar hpHstar hcweight hweight heventParent hcutsParent hξ0 haLoad0 hη0
    bin cin deep βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap mGeom ell cover loss fout binner crossout Aroot Croot Xf Zf
    hmGeom hlamGeom hgeometry Ncert N hNcert hNsize hterminal δend ζh ζe γ eCoeff hδend hRend hHend hRateEnd hRate0 hζh hζe hγ hCoeff hlam0 hlam1
    cert hcert hs_m hs_k hs_load hs_α hs_ω hs_β hs_bRoot hs_BRoot hs_δ hs_εstar hs_ηpack hs_p hs_εgeom
    hs_βe hs_βh hs_bHub hs_BHub hs_ηhub hs_Ncert hs_δend hs_ζhub hs_ζlocal hs_γ
    hParentRate hβeEq hβhEq hb₀ hLconf hpack hκ hp₀R hp₀H Nfinish M rateFinish θmatch ellCap finishCap kcap
    hθmatch hθcap hεsup hpθ hsqrt hbase hM hell hcoverCap hbudget hsched
  have hsample:=ordinary_actual_trace_sharp_from_selected_geometry mWheel loadK d hmWheel ρ₀ pmin hmin href δcut ζcut εcut ζlimit εsample
    ε ξ aLoad a ρ θ β η ηProfile α ζ cBoundary δ rate C rateParent mBalance mCover mInitial ηInitial δInitial
    hInitialAt hbalance hcover hζlim hζrate hζcut hεcut hζlimit
    V U Γ Color P Gbase G Hbase Hs D m hreg hn hD hρlo hρhi hmB hmC Q π hπ σ coins j s Kres cost i hi
    A pR pH θhost εR εH βe βh αcut pstar ηf bPair Bweight capHub hζcap hfamily
    hpRlo hpRhi hpHlo hpHhi hθhost hdegree hpEq hs hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβe hβh0 hβh hPairRim hPairSpoke havoid hgood htrace hstate
    L hiL hρpos hβ0 hβ1 hεpos hm0 hgood2 inner cross huniform hcost hmI hεRinitial hεHinitial hηInitial hbal hdiv hdeep hrim hpH hcut hhref
    k hk βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale hroot hN
    βP ηP row εTri weight hinputs hpRstar hpHstar hcweight hweight heventParent hcutsParent hξ0 haLoad0 hη0
    βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap mGeom hmGeom hlamGeom hgeometry Ncert N hNcert hNsize hterminal
    δend ζh ζe γ eCoeff hδend hRend hHend hRateEnd hRate0 hζh hζe hγ hCoeff
  obtain ⟨hsharp,hwin0,hprofile,hnear,hLrate,hfine,hcross,hdeepbal,hweights,hpair⟩:=hsample
  have hgeo:=hgeometry V U P D m hreg hn hD hρlo hρhi hmGeom Q i hi
  obtain ⟨hTW,hT,hW,_,_,_,_,_,_⟩:=hgeo
  have htrace':OrdinaryProtectedTrace (Gbase\ordinaryResourceRim Gbase Kres)
      (fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈Kres))
      (fun k=>Q.extendedVertices (k+1)) (fun k=>Q.extendedVertices (k+2))
      (fun k=>Q.extendedIndices (k+1)) (fun k=>Q.extendedIndices (k+2)) cost (ordinaryFineDeepCost Q ξ) (i+1) A:=htrace
  have hlocal:=ordinary_protected_trace_certificate_from_local_data cert hcert P Gbase G Hbase Hs D m β ε Q π hπ d σ Kres
    hPairRim cost (ordinaryFineDeepCost Q ξ) i A
  dsimp only [OrdinaryTraceCertificateFromLocalDataAt] at hlocal
  simp only [hs_m,hs_k,hs_load,hs_α,hs_ω,hs_β,hs_bRoot,hs_BRoot,hs_δ,hs_εstar,hs_ηpack,hs_p,hs_εgeom,
    hs_βe,hs_βh,hs_bHub,hs_BHub,hs_ηhub,hs_Ncert,hs_δend,hs_ζhub,hs_ζlocal,hs_γ] at hlocal
  have hprofile':=hprofile
  rw [hβeEq,hβhEq] at hprofile'
  have hL0:0≤Ledit:=by dsimp [Ledit];positivity
  have hout:=hlocal ξ aLoad lamGeo bin cin deep (βparent/2) (2*hRef-ζparent) (εparent+gap) ξreserve ζout
    pR pH (θhost+α-β/2) Ledit ρ₀ εR εH eCoeff hParentRate (fun u=>s (g u)) j
    htrace' hstate (by simpa only [hs_m] using hbal) (by simpa only [hs_m] using hdiv) hb₀ hLconf hpack
    (by convert hprofile' using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hweights using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hpair using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hT using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hW using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hTW using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hsharp using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hκ hp₀R hp₀H hpHhi hεR0 hεH0 hL0 Nfinish M rateFinish θmatch ellCap finishCap kcap hθmatch
    (by simpa only [hs_ζhub,hs_ζlocal,hs_γ] using hθcap)
    (by simpa only [hs_p] using hεsup) (by simpa only [hs_p] using hpθ) (by simpa only [hs_p] using hsqrt)
    hξ0 haLoad0 hlam0 hlam1 (by simpa only [hs_Ncert] using hbase) hM
    (by simpa only [hs_load,hs_m] using hell) hcoverCap hbudget
    (by simpa only [hs_m,hs_βe,hs_βh,hs_p] using hsched)
  convert hout using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
end Oberwolfach
