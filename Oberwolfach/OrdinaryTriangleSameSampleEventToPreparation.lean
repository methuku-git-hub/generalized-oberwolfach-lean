module

public import Oberwolfach.OrdinaryOriginalTriangleNamedTestsWitness
public import Oberwolfach.OrdinaryTriangleNamedTestsExternalFailureBudgetSeparateLists

@[expose] public section
/-! Attach the original high-probability matching, correction, level and
endpoint event to the terminal preparation transfer on the same sample.
The remaining local wheel callback is displayed explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 90000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_same_sample_event_to_preparation
    (m k d K mv mAbs aAbs bAbs Nsel Ncorr Nc Ng Nh Ncol Ngeom Nplace dNeed N₀ M:ℕ) (hd:2≤d)
    (βfreq ρ₀ α θ θhost lamMatch aRow γ capSel lamSel ζDel τ tMatch ξMatch bMatch σbal ζevent
      χpair χlist χbal χbd χnbr χpairR χpath aEvent ε εabs εv βv ξAbs χlocal χglobal χhub χcol:ℝ)
    (BO:Fin K→ℝ)
    (hsel:OrdinaryOriginalThresholdForAllFactors 3 m k d K hd Nsel βfreq ρ₀ α θ θhost
      lamMatch aRow γ capSel lamSel ζDel (βfreq/200) τ tMatch ξMatch bMatch BO ζevent χpair χlist σbal χbal χbd χnbr χpairR χpath aEvent)
    (hgeom:OrdinaryFirstVortexCorrectionThresholdShape Ngeom Nc Ng Nh Ncol θhost α ρ₀ βfreq ε εabs εv)
    (hcorr:OrdinaryWeightedCorrectionAfterLocalThresholds 3 d hd mAbs aAbs bAbs (2*mv) mv 10 Ncorr Nc Ng Nh Ncol
      (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) εabs εv (2*((3*d:ℕ):ℝ)) ξAbs (θ/2) χlocal χglobal χhub χcol (2/ε))
    (η capEdit αplace lamPlace ζPlace δ κplace bplace zplace matchErr κprime ζret ξedit rate ξroot:ℝ)
    (hm:7≤m) (hK:0<K) (hda:1/θ≤d) (hη:0<η) (hcapEdit:capEdit≤η)
    (hstage:OrdinaryPlacementStage m dNeed αplace lamPlace ζPlace capEdit δ θ κplace bplace zplace matchErr σbal κprime)
    (hafter:OrdinaryPlacementAfterSpacing m d Nplace αplace δ θ κplace bplace zplace matchErr ζret)
    (hmatching:OrdinaryPlacementMatchingRateBounds K θ κprime bplace zplace δ matchErr lamMatch aRow γ)
    (hξedit:0≤ξedit) (hξσ:ξedit≤σbal)
    (hterminal:OrdinaryOriginalTerminalConditionalPreparationSeparateListsAt 3 m k d K hd βfreq ρ₀ α θhost ε βv
      δ θ aRow γ σbal lamMatch lamPlace ξedit bMatch rate ξroot mAbs (2*mv) aAbs bAbs)
    (χ capFailure:ℝ) (Nfailure:ℕ) (hfailure:OrdinaryTriangleFailureBudgetBeforeAbsorber χ capFailure Nfailure)
    (hζ:ζevent≤capFailure) (hχpair:χpair≤capFailure) (hχlist:χlist≤capFailure) (hχbal:χbal≤capFailure)
    (hχbd:χbd≤capFailure) (hχnbr:χnbr≤capFailure) (hχpairR:χpairR≤capFailure) (hχpath:χpath≤capFailure)
    (hχcol:χcol≤capFailure) (hχhub:χhub≤capFailure) (hχglobal:χglobal≤capFailure) (hχlocal:χlocal≤capFailure)
    (hρ:0<ρ₀) (hα:0<α) (hθhost:1/2≤θhost) (hβfreq:0<βfreq) (hε:0<ε) (hmv:0<mv) (hAbs:2*mv≤mAbs)
    (hβv:0≤βv) (hβv1:βv≤1/4) (hN₀:N₀≤M) (hsize:2/ε≤(M:ℝ)) (htermSize:(M:ℝ)≤ε*mv/2)
    (v₀:ℕ) (κ aLoad ξdeep b Bweight ηHub δcap χdeep χHub εR εH χone χtwo χcut:ℝ)
    (htri:OrdinaryTriangleHubAfterSpacing d v₀ hd (α/2) ρ₀ (ρ₀*(βfreq/200)/2) κ aLoad ε ξdeep b Bweight ηHub δcap εR εH χdeep χHub χone χtwo χcut βv)
    (hdeepSize:v₀≤mv)
    (kParent Mhost Mcut:ℕ) (βP ηP ηH βH cParent Bparent εTri χhost δref href χref:ℝ)
    (hpstar:0<ρ₀*(βfreq/200)/2)
    (hselector:OrdinaryTriangleFixedDomainSelector kParent d Mhost hd (max (1/2) (cycleThreshold 3))
      (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16) βP ηP ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hpstar)
    (hcuts:OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) (ρ₀*(βfreq/200)/2)
      (ρ₀/16) δref href ε χref (2*(3*d)))
    (hε1:ε≤1) (hερ:ε≤ρ₀/16) (hβα:βv≤α/8) (hβε:βv≤εTri)
    (hMhost:(Mhost:ℝ)≤ε*mv/2) (hMcut:(Mcut:ℝ)≤ε*mv/2)
    (cInner CInner ξInner bInner BInner ηInner Kdom eParent hParentRate capInner χinner χendpoint tpot:ℝ) (vInner:ℕ)
    (hInner:OrdinaryTriangleInnerEndpointHostSelector (α/2) cInner CInner ε ρ₀ (ρ₀*(βfreq/200)/2)
      ξInner bInner BInner ηInner Kdom eParent hParentRate capInner χinner χendpoint tpot d hd βv vInner)
    (hvInner:vInner≤mv)
    (hi:χinner≤capFailure) (hdp:χdeep≤capFailure) (h1:χone≤capFailure) (h2:χtwo≤capFailure)
    (hc:χcut≤capFailure) (hhost:χhost≤capFailure) (href':χref≤capFailure) (hHub:χHub≤capFailure) (hend:χendpoint≤capFailure):
    ∃N:ℕ,∀n qCount D:ℕ,N≤n→qCount≤n→
    ∀(F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2),
      (∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=3)).card:ℝ))→
      (∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θhost)→
    ∀(Allowed:Set ℕ),(∀u,AllowedCycleLengths (F u) Allowed)→
    ∀(P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→(θhost+α)*(n:ℝ)≤D→
      ρ₀≤ initialIndexDensity (Fin qCount) D→ initialIndexDensity (Fin qCount) D≤1→
    ∀(Q:Vortex (Fin qCount) P D βv ε mv) (π:Equiv.Perm (Fin n))
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∃(i₀:Fin K) (rsv:ℝ) (Cres:∀u,Finset (F u).ConnectedComponent)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ (βfreq/200) d)
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
      (seed:(Fin (m+1)→Fin n)→ℝ),
      OrdinaryOriginalSelectorFactorWitness n qCount D 3 m k d K hd
        ρ₀ θ lamMatch aRow γ lamSel ζDel (βfreq/200) τ tMatch ξMatch bMatch σbal ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent α
        BO F hF P π i₀ rsv Cres sampling w seed ∧
      OrdinaryFirstVortexCorrectionPointShape n qCount D K mv d 3 Nc Ng Nh Ncol
        θhost α ρ₀ βfreq ε εabs εv P F hF i₀ rsv θ ((m:ℝ)+1) βv Q ∧
      (∀i,i<Q.length→OrdinaryDeepCoverLevelInputs 2 (2*(3*d)) d (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16) 1 εTri
        (P.comap (markedVortexVertexEmbedding Q i).toEmbedding) ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i).toEmbedding)
        (markedVortexPermutation Q π hπ i) (markedVortexInnerHubs Q i)
        (2*(initialIndexDensity (Fin qCount) D*rsv/2)) rsv
        (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity (Fin qCount) D) βv) ∧
      ∃selection:OrdinaryTriangleFullDomainSelection kParent d hd (max (1/2) (cycleThreshold 3))
        (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16) βP ηP ηH βH cParent Bparent εTri χhost (2*(3*d)) hpstar
        (Fin n) (Fin qCount) Bool Bool (markedVortexVertexType Q) (markedVortexHubType Q)
        P (permutationConflictGraph π (3*d)) (fun i=>(markedVortexVertexEmbedding Q i).toEmbedding)
        (fun i=>markedVortexHubEmbedding Q i) (markedVortexPermutation Q π hπ) (Q.length-1),
      ∀{R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let E:=OrdinaryAssignedCorrectionEvent 3 d mAbs aAbs bAbs (2*mv) 10 n qCount K D hd
      (θ/2) χlocal χglobal χhub χcol ξAbs P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
      R ρ ζevent χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γ σbal aEvent ζDel lamSel bMatch w seed tMatch ξMatch
    ∃endpointWeight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ,
    let Tests:=fun z:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)=>
      OrdinaryTriangleSameSampleLevelEndpointTests D mv kParent d βv ε P Q π hπ
        (α/2) ρ₀ (ρ₀*(βfreq/200)/2) βP ηP ηH βH cParent Bparent εTri δref href (2*p) rsv κ aLoad εR εH
        cInner (4*CInner/(ρ₀*(βfreq/200)/2)^7) ηInner capInner (eParent*ε) (hParentRate*ε) θhost tpot
        s selection.weight endpointWeight z.1.1 z.2;
    (∀z,E z→Tests z→
      (∀u (c:↥(Cres u)),Fintype.card c.val=2+1)→
      cycleThreshold 3≤θhost→
      (∀i,i<Q.length→N₀≤Fintype.card (markedVortexVertexType Q i))→
      (∀Kres JQ JH,
        let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)
        let Bad:=permutationConflictGraph π (3*d)
        let Reference:=rawWheelGraph P raw\Bad
        let Href:=rawWheelSpokes π d raw false;
        OrdinaryCorrectedProtectedReservoirWitness 3 mAbs (2*mv) aAbs bAbs ξAbs Reference Bad Href
          (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
          (Q.extendedIndices Q.length) (Q.extendedIndices 1) Kres JQ JH→
        let cost:=ordinaryTriangleAssignedReservoirCost d δ aRow γ ξedit σbal sampling.u Kres;
        0≤cost ∧ cost≤14*η*n ∧ cost+2*((3*d:ℕ):ℝ)≤15*η*n)→
      OrdinaryTriangleUniformMatchedWheelOutcome (mAbs:=mAbs) (tAbs:=2*mv) (aAbs:=aAbs) (bAbs:=bAbs)
        d P D mv βv ε rate ξroot Q π F Cres (Finset.univ\Q.extendedVertices 1)
        (Q.extendedVertices Q.length) (Q.extendedIndices Q.length) ξAbs
        (ordinaryTriangleAssignedReservoirCost d δ aRow γ ξedit σbal sampling.u) z.1.1)→
    let aBound:=2^((2*mv)*(2*mv))*aAbs;let bBound:=2^((2*mv)*(2*mv))*bAbs;
    1-χ-1/(n:ℝ)^10≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (initialIndexDensity (Fin qCount) D)
      (by unfold initialIndexDensity;positivity)
      (by rw [←sampling.hphysical];exact sampling.hsum))).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) (Q.extendedVertices 1) ξedit (aBound*aBound+aBound*bBound) F)
 :=by
  obtain ⟨Ntransfer,htransfer⟩:=ordinary_triangle_named_tests_external_failure_budget_separate_lists m k d K hd βfreq ρ₀ α θhost ε βv
    δ θ aRow γ σbal lamMatch lamPlace ξedit bMatch rate ξroot mAbs (2*mv) aAbs bAbs Nplace dNeed N₀ M hN₀ hε hsize hβv hβv1
    η capEdit αplace ζPlace κplace bplace zplace matchErr κprime ζret hm hK hda hη hcapEdit hstage hafter hmatching hξedit hξσ hρ hα hθhost hβfreq hterminal χ capFailure Nfailure hfailure
  refine ⟨max 2 (max Ntransfer (max Nsel (max Ngeom Ncorr))),?_⟩
  intro n qCount D hn hq F hF habundance hthreshold Allowed hAllowed P hreg hdegree hρlo hρhi Q π hπ hnoshort
  obtain ⟨i₀,rsv,Cres,sampling,w,seed,hwitness,hpoint,hinputs,selection,hprob⟩:=
    ordinary_original_triangle_named_tests_witness n qCount D m k d K mv mAbs aAbs bAbs 10 Nsel Ncorr Nc Ng Nh Ncol Ngeom hd
      βfreq ρ₀ α θ θhost lamMatch aRow γ capSel lamSel ζDel τ tMatch ξMatch bMatch σbal ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent ε εabs εv βv ξAbs χlocal χglobal χhub χcol
      BO hsel hgeom hcorr (by omega) (by omega) (by omega) (by omega) hq hmv hρ hε F hF habundance hρlo hρhi hthreshold P hreg π hdegree hθhost hα hnoshort Q hπ hβv hβv1
      v₀ κ aLoad ξdeep b Bweight ηHub δcap χdeep χHub εR εH χone χtwo χcut htri hβfreq hdeepSize (fun _=>eParent*ε) (fun _=>hParentRate*ε)
      kParent Mhost Mcut βP ηP ηH βH cParent Bparent εTri χhost δref href χref hpstar hselector hcuts hε1 hερ hβα hβε hMhost hMcut
      cInner CInner ξInner bInner BInner ηInner Kdom eParent hParentRate capInner χinner χendpoint tpot vInner hInner hvInner
  refine ⟨i₀,rsv,Cres,sampling,w,seed,hwitness,hpoint,hinputs,selection,?_⟩
  intro R _ ρ p p₂ q s μ E
  obtain ⟨endpointWeight,hprob'⟩:=hprob (R:=R) ρ
  refine ⟨endpointWeight,?_⟩
  intro Tests hWheel aBound bBound
  exact htransfer n qCount D (by omega) hq F hF habundance hthreshold Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hπ hnoshort hmv htermSize
    i₀ rsv Cres sampling w seed τ tMatch ξMatch capSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness
    kParent βP ηP ηH βH cParent Bparent εTri δref href κ aLoad εR εH cInner CInner ηInner capInner eParent hParentRate tpot selection.weight endpointWeight
    χlocal χglobal χhub χcol ξAbs χinner χdeep χone χtwo χcut χhost χref χHub χendpoint R ρ
    hζ hχpair hχlist hχbal hχbd hχnbr hχpairR hχpath hχcol hχhub hχglobal hχlocal hi hdp h1 h2 hc hhost href' hHub hend hprob' hAbs hWheel
end Oberwolfach
