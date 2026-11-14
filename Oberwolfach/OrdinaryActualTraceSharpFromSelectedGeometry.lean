module

public import Oberwolfach.OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold
public import Oberwolfach.OrdinaryVortexAsymmetricPairingFromVertexRate
public import Oberwolfach.OrdinaryActualTraceFineCoverAtLocalHost
public import Oberwolfach.OrdinaryProtectedPairTraceLocalHost
public import Oberwolfach.OrdinaryProtectedPairTraceHubBalanceLocalHost
public import Oberwolfach.OrdinaryActualTraceBalanceAndFineCoverAt
public import Oberwolfach.OrdinaryActualInitialAmbientBalance
public import Oberwolfach.OrdinaryVortexActualUniformTwoStepBalance
public import Oberwolfach.OrdinaryVortexActualUniformTwoStepDeepBalance
public import Oberwolfach.OrdinaryProtectedPairTraceHubBalance
public import Oberwolfach.OrdinaryProtectedPairTracePhysicalEdit
public import Oberwolfach.OrdinaryVortexLocalSharpSeparateCross
public import Oberwolfach.OrdinaryUniformInnerHubEvent
public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent
public import Oberwolfach.OrdinaryProtectedTraceHostLe
public import Oberwolfach.OrdinaryVortexTraceFullParentGeneralFineSharpReferenceGeneralLoad
public import Oberwolfach.OrdinaryInducedBalanceToSpanning
public import Oberwolfach.OrdinaryDeepTracePairingParentAt
public import Oberwolfach.OrdinaryVortexUniformTwoStepBalanceFromInitial
public import Oberwolfach.OrdinaryVortexUniformTwoStepDeepBalance
public import Oberwolfach.OrdinaryDeepTraceCoverAndSeparatedBalanceOrdered

@[expose] public section
/-! Apply the preselected cover and balance callbacks to one protected trace
and the same sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_trace_sharp_from_selected_geometry
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
      rateParent≤δend*ε/8→0≤rateParent→0<ζh→0<ζe→0<γ→γ≤eCoeff→
    (∃Droot:OrdinaryRootCoverNonrootData Gloc Floc Hloc I T B W (mWheel+1) cover ell,
      Nonempty (OrdinaryRootCoverSharpReferenceData Ploc Gloc Floc Hloc I T B W (mWheel+1) k (by omega)
        cover ell bin cin deep loss Droot α (ρ₀/16) (βparent/2) βout (cweight*(1-δparent)^mWheel)
        (B0/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*hRef-ζparent) (δparent/2) (εparent+gap)
        ((εparent+gap)+geomGap) ηpack ξreserve ζout p εout fout binner crossout)) ∧
    0≤(∑t∈Jwin,cost t) ∧
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH (θhost+α-β/2)
      (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤η*I.card) ∧
    Ledit≤rateParent*Fintype.card (markedVortexVertexType Q (i+1)) ∧
    OrdinaryFineWheelCoverResult mWheel loadK ξ aLoad Gloc Floc Hloc I T B W ∧
    (∀v,v∉I→|((Gloc.neighborFinset v∩I).card:ℝ)-2*(B.filter (Hloc v)).card|≤
      ηInitial*I.card+2*(ordinaryFineDeepCost Q ξ) i) ∧
    (∀v,v∉T→|((Gloc.neighborFinset v∩T).card:ℝ)-2*(W.filter (Hloc v)).card|≤
      (initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+
        3*(2*((3*d:ℕ):ℝ))+2*(ordinaryFineDeepCost Q ξ) i) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel bPair Bweight ηf Gloc Floc Hloc I B) ∧
    OrdinaryVortexAsymmetricPairingGeometryAt Q (i+1) Ncert ρ₀ δend εR εH Ledit ζh ζe γ eCoeff:=by
  intro V U Γ Color _ _ _ _ _ _ P Gbase G Hbase Hs D m hreg hn hD hρlo hρhi hmB hmC Q π hπ σ coins j s Kres cost i hi
    A pR pH θhost εR εH βe βh αcut pstar f g I T B W ρi Ploc Floc Gloc Hloc raw F R J S H S₀ H₀ X Tdeep Z Wdeep Jwin Ledit
    ηf bPair Bweight capHub hζcap hfamily
    hpRlo hpRhi hpHlo hpHhi hθhost hdegree hpEq hs hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβe hβh0 hβh hPairRim hPairSpoke havoid hgood htrace hstate L hiL hρpos hβ0 hβ1 hεpos hm0 hgood2 inner cross huniform hcost hmI hεRinitial hεHinitial hηInitial hbal hdiv hdeep hrim hpH hcut hhref
    k hk βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale hroot hN
    βP ηP row εTri weight hinputs hpRstar hpHstar hcweight hweight heventParent hcutsParent hξ0 haLoad0 hη0
    bin cin deep βout ηpack ξreserve ζout p εout lamGeo γgeom edit βeGeo βhGeo geomGap mGeom ell cover loss fout binner crossout Aroot Croot Xf Zf
    hmGeom hlamGeom hgeometry Ncert N hNcert hNsize hterminal δend ζh ζe γ eCoeff hδend hRend hHend hRateEnd hRate0 hζh hζe hγ hCoeff
  have hgeom:=hgeometry V U P D m hreg hn hD hρlo hρhi hmGeom Q i hi
  obtain ⟨hsizeGeo,hT,hW,hdeep0,hbin0,hcin0,hstatic,hscaleV,hscaleU⟩:=hgeom
  have hsize:(T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q (i+1)):=
    hsizeGeo.trans (mul_le_mul_of_nonneg_right hlamGeom (by positivity))
  obtain ⟨hwin0,hwinI,hwinB,hprofile,hnearProfile,hmarginProfile,hLinner,hLparent⟩:=
    hbalance V U Γ Color P Gbase Hbase D m hreg hn hD hρlo hρhi hmB Q π hπ s j σ
      pR pH θhost εR εH βe βh hpRlo hpRhi hpHlo hθhost hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
      Kres hPairRim hPairSpoke havoid hgood cost (ordinaryFineDeepCost Q ξ) i hi A G Hs htrace hstate hcost
  have hboth:=ordinary_vortex_actual_uniform_two_step_balance_from_initial ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial hInitialAt
    P Gbase G Hbase Hs D m hreg hn hD hρlo hρhi hmI Q π hπ pR pH θhost εR εH βe βh s j σ Kres
    hpRlo hpRhi hpHlo hθhost hdegree hεR0 hεRinitial hεH0 hεHinitial hβe0 hβe hβh0 hβh hpEq hs hPairRim hPairSpoke havoid hgood
    (mWheel+1) i L hi hiL cost (ordinaryFineDeepCost Q ξ) A inner cross huniform hstate
  have hnear:∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤η*I.card:=by
    intro v
    have hle:=mul_le_mul_of_nonneg_right hηInitial (show (0:ℝ)≤I.card by positivity)
    have hh:=hboth.1 v
    convert hh.trans hle using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hI0:0≤(I.card:ℝ):=by positivity
  have hW0:0≤(Fintype.card (markedVortexVertexType Q (i+1)):ℝ):=by positivity
  have hLcover:Ledit≤ζlimit*I.card:=hLinner.trans (mul_le_mul_of_nonneg_right hζlim hI0)
  have hLrate:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q (i+1)):=
    hLparent.trans (mul_le_mul_of_nonneg_right hζrate hW0)
  have hL0:0≤Ledit:=by dsimp [Ledit];positivity
  have hLcap:Ledit≤capHub*I.card:=hLinner.trans (mul_le_mul_of_nonneg_right hζcap (by positivity))
  have hevent:=hfamily (i+1) hi Ledit hL0 hLcap
  have hlocalHost:(G.comap f)≤(P.comap f):=by
    have hs:=ordinary_protected_pair_trace_local_host P Gbase Hbase D m β ε Q π d σ Kres
      (Q.extendedVertices 1) (by rfl) hPairRim cost (ordinaryFineDeepCost Q ξ) i A G Hs htrace hstate
    exact hs.trans sdiff_le
  have hh:=hcover V U Γ Color P Gbase G Hbase Hs D m hreg hn hD hρlo hρhi hmC Q π hπ σ coins j s Kres cost (ordinaryFineDeepCost Q ξ) i hlocalHost hi
    A pR pH (θhost+α-β/2) εR εH Ledit βe βh αcut pstar θhost α hpHlo hεRsample hεHsample hLcover
    hprofile rfl hεR0 hεH0 hdegree hpEq hgood hnear htrace hstate hbal hdiv hdeep hrim hpH hpHhi hεcut hζcut hζlimit hL0 hcut hhref
  have hdeepBal:=ordinary_vortex_actual_uniform_two_step_deep_balance P Gbase Hbase D m β ε pR pH εR εH Q π hπ d s j σ Kres
    hn hreg hρpos hβ0 hpH.le hεR0 hεH0 hpEq hPairRim hPairSpoke havoid hgood2 (mWheel+1) i L hi hiL cost (ordinaryFineDeepCost Q ξ) A G Hs inner cross huniform hstate
  have hlocal:Gloc≤Ploc:=hlocalHost
  have hweights:=hevent Gloc Hloc (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hlocal
  have hcost_i:0≤cost i:=by
    have hiwin:i∈Jwin:=by simp [Jwin]
    exact (hcost i hiwin).1
  have hLrate':2*((3*d:ℕ):ℝ)+cost i≤rateParent*Fintype.card (markedVortexVertexType Q (i+1)):=by
    simpa [Ledit,Jwin] using hLrate
  have hTX:T⊆I:=(ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)).2.2.1
  have hWZ:W⊆B:=(ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)).2.2.2
  have hbin:0≤bin:=by dsimp [bin];positivity
  have hinner:=ordinary_induced_balance_to_spanning Gloc Hloc I B bin hbin hnear
  have hBundle:=ordinary_protected_pair_trace_hub_balance_local_host mWheel P Gbase Hbase D m β ε Q π hπ d s j σ
    Kres (Q.extendedVertices 1) (by rfl) hPairRim pR pH (θhost+α-β/2) εR εH βe βh bPair Bweight ηf capHub hfamily
    cost (ordinaryFineDeepCost Q ξ) i hi A G Hs Ledit hL0 hLcap htrace hstate hbal hdiv
    (by convert hprofile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
  obtain ⟨hhost,_hevent,_hhub,hlocalBal,hlocalDiv⟩:=hBundle
  have hFdegree:∀v,(F.degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    exact_mod_cast permutationConflictGraph_degree_le π (3*d) v
  have hphysical:=ordinary_protected_pair_trace_physical_edit P Gbase F Hbase D m β ε Q π hπ d j σ Kres
    (Q.extendedVertices 1) (Q.extendedIndices 1) (by rfl) (by rfl) hPairRim hPairSpoke havoid
    (2*((3*d:ℕ):ℝ)) (by positivity) hFdegree cost (ordinaryFineDeepCost Q ξ) i 2 (by omega) hi A G Hs htrace hstate
  have hRefResult:=ordinary_vortex_local_fine_sharp_separate_cross_general_load mWheel loadK 2 hmWheel (by omega)
    βH ηH B0 ρ₀ pstar βparent εparent ζparent rateParent N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale
    k hk α cweight hRef δparent gap lam hroot P G Hs D m β ε Q (i+1) hi π hπ d j σ coins s
    βP ηP row εTri pR pH η cin Ledit weight hreg hn hD hρlo hρhi hβ0 hβ1 hεpos hm0 hN hL0 hLrate
    (by convert hhost using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hlocalBal using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hlocalDiv using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hinputs using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    hpRstar hpRhi hpHstar hpHhi hcweight hweight
    (by convert heventParent using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hcutsParent using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hphysical z using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    hη0 (by intro v;convert hnear v using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert hboth.2 v hv using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    ξ aLoad bin cin deep (ρ₀/16) βout ((εparent+gap)+geomGap) ηpack ξreserve ζout p εout
    hsize hξ0 haLoad0 hbin hdeep0 (by dsimp [bin];rfl) le_rfl hh
    (by intro v hv;convert hdeepBal v hv using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hstatic using 1 <;> congr! 10 <;> first | exact Subsingleton.elim _ _ | (ext x;simp))
    (by convert hscaleV using 1 <;> congr! 10 <;> first | exact Subsingleton.elim _ _ | ring | (ext x;simp [Aroot,Croot]))
    (by convert hscaleU using 1 <;> congr! 10 <;> first | exact Subsingleton.elim _ _ | ring | (ext x;simp [Aroot,Croot]))
  refine ⟨?_,hwin0,?_,?_,hLrate,?_,?_,?_,?_,?_⟩
  · convert hRefResult using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v;convert hnear v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv
    convert hboth.2 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv
    convert hdeepBal v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hweights using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · exact ordinary_vortex_asymmetric_pairing_from_vertex_rate Q hreg hn hD hρ₀ hρlo hρhi hβ0 hβ1 hεpos hm0 (i+1) hi
      Ncert N hNcert hNsize hterminal δend εR εH rateParent rateParent Ledit hδend hRend hHend hRateEnd
      hRate0 le_rfl hLrate ζh ζe γ eCoeff hζh hζe hγ hCoeff
end Oberwolfach
