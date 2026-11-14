module

public import Oberwolfach.OrdinaryOriginalDeepParentLevelWitness
public import Oberwolfach.OrdinaryAssignedLookbackBalanceOnPriorSplit
public import Oberwolfach.OrdinaryOriginalDeepParentVortexWitness
public import Oberwolfach.OrdinaryOriginalParentLevelInputs
public import Oberwolfach.OrdinaryOriginalParentAttachPrior
public import Oberwolfach.OrdinaryDeepRowsCutsNamedProbability

@[expose] public section
/-! Choose the original selector witnesses once and retain the correction
and non-triangle all-level event on their common assigned sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_deep_parent_lookback_balance_witness
    (n qCount D rstar m k d K mv mAbs aAbs bAbs q₀ Nsel Ncorr Nc Ng Nh Ncol Ngeom:ℕ) (hd:2≤d)
    (βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent ε εabs εv βv ξAbs χlocal χglobal χhub χcol:ℝ)
    (BO:Fin K→ℝ)
    (hsel:OrdinaryOriginalThresholdForAllFactors rstar m k d K hd Nsel βfreq ρ₀ α θ θhost
      lam aRow γ cap lamList ζDel (βfreq/200) τ tMatch ξMatch bMatch BO ζ χpair χlist σ χbal χbd χnbr χpairR χpath aEvent)
    (hgeom:OrdinaryFirstVortexCorrectionThresholdShape Ngeom Nc Ng Nh Ncol θhost α ρ₀ βfreq ε εabs εv)
    (hcorr:OrdinaryWeightedCorrectionAfterLocalThresholds rstar d hd mAbs aAbs bAbs (2*mv) mv q₀ Ncorr Nc Ng Nh Ncol
      (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) εabs εv (2*((3*d:ℕ):ℝ)) ξAbs (θ/2) χlocal χglobal χhub χcol (2/ε))
    (hnsel:Nsel≤n) (hngeom:Ngeom≤n) (hncorr:Ncorr≤n) (hn:2≤n) (hq:qCount≤n) (hmv:0<mv)
    (hρ:0<ρ₀) (he:0<ε)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (habundance:∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ))
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D) (hρhi:initialIndexDensity (Fin qCount) D≤1)
    (hthreshold:∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θhost)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (π:Equiv.Perm (Fin n))
    (hdegree:(θhost+α)*(n:ℝ)≤D) (hθ:(1/2:ℝ)≤θhost) (hα:0<α)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Qlook:VortexLookback (Fin qCount) P D βv ε mv 2)
    (hπ:∀i x,π x∈Qlook.toVortex.extendedVertices i↔x∈Qlook.toVortex.extendedVertices i) (hβv:0≤βv) (hβv1:βv≤1/4)
    (Kdeep v₀:ℕ)
    (αcut c C a ε₀ ρdeep θdeep aLoad ξdeep b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsAfterSpacing (rstar-1) Kdeep d hd v₀ βv
      (α/2) ρ₀ (ρ₀*(βfreq/200)/2) αcut c C a ε₀ ρdeep θdeep aLoad ε ξdeep b Bweight ηHub Kdom
      χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hdeepSize:v₀≤mv) (density tR tH:ℕ→ℝ)
    (kParent Mhost Mcut:ℕ) (hmParent:3≤rstar-1)
    (βP ηP row ηH βH cParent Bparent εTri χhost δref href χref:ℝ)
    (hpstar:0<ρ₀*(βfreq/200)/2)
    (hselector:OrdinaryGeneralFixedDomainSelector (rstar-1) kParent d Mhost hmParent hd
      (max (1/2) (cycleThreshold ((rstar-1)+1))) (α/2) (ρ₀*(βfreq/200)/2)
      (ρ₀/16) βP ηP row ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hpstar)
    (hcuts:OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) (ρ₀*(βfreq/200)/2)
      (ρ₀/16) δref href ε χref (2*(3*d)))
    (hε1:ε≤1) (hερ:ε≤ρ₀/16) (hβα:βv≤α/8) (hβε:βv≤εTri)
    (hM:(Mhost:ℝ)≤ε*mv/2) (hMcut:(Mcut:ℝ)≤ε*mv/2)
    (χthree:ℝ) (mBalance:ℕ) (hmBalance:mBalance≤mv)
    (hBalanceAt:OrdinaryThreeStepBalanceProductAt d hd εR εH βv ε ρ₀ χthree mBalance):
    let Q:=Qlook.toVortex;
    ∃(i₀:Fin K) (rsv:ℝ) (Cres:∀u,Finset (F u).ConnectedComponent)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ (βfreq/200) d)
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
      (seed:(Fin (m+1)→Fin n)→ℝ),
      OrdinaryOriginalSelectorFactorWitness n qCount D rstar m k d K hd
        ρ₀ θ lam aRow γ lamList ζDel (βfreq/200) τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent α
        BO F hF P π i₀ rsv Cres sampling w seed ∧
      OrdinaryFirstVortexCorrectionPointShape n qCount D K mv d rstar Nc Ng Nh Ncol
        θhost α ρ₀ βfreq ε εabs εv P F hF i₀ rsv θ ((m:ℝ)+1) βv Q ∧
      (∀i,i<Q.length→OrdinaryDeepCoverLevelInputs (rstar-1) (2*(3*d)) d (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16) 1 εTri
        (P.comap (markedVortexVertexEmbedding Q i).toEmbedding) ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i).toEmbedding)
        (markedVortexPermutation Q π hπ i) (markedVortexInnerHubs Q i)
        (2*(initialIndexDensity (Fin qCount) D*rsv/2)) rsv
        (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity (Fin qCount) D) βv) ∧
      ∃selection:OrdinaryGeneralFullDomainSelection (rstar-1) kParent d hmParent hd
        (max (1/2) (cycleThreshold ((rstar-1)+1))) (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16)
        βP ηP row ηH βH cParent Bparent εTri χhost (2*(3*d)) hpstar (Fin n) (Fin qCount) Bool Bool
        (markedVortexVertexType Q) (markedVortexHubType Q) P (permutationConflictGraph π (3*d))
        (fun i=>(markedVortexVertexEmbedding Q i).toEmbedding) (fun i=>markedVortexHubEmbedding Q i)
        (markedVortexPermutation Q π hπ) (Q.length-1),
      ∀{R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let E:=OrdinaryAssignedCorrectionEvent rstar d mAbs aAbs bAbs (2*mv) q₀ n qCount K D hd
      (θ/2) χlocal χglobal χhub χcol ξAbs P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
      R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lam aRow γ σ aEvent ζDel lamList bMatch w seed tMatch ξMatch
    let loss0:=(((((((0+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath)
    let loss:=loss0+χcol+χhub+χglobal+2/(n:ℝ)^q₀+(1/(n:ℝ)+2/(n:ℝ)^2)+χlocal;
    let Good:=OrdinaryDeepRowsCutsEvent n qCount D mv (rstar-1) Kdeep d βv ε P Q π hπ
      p rsv (ρ₀*(βfreq/200)/2) αcut c C b Bweight ξdeep ηHub Kdom a aLoad ρdeep θdeep capDeep eParent hParent εR εH
      density tR tH s false R μ ρ E loss χinner χdeep χone χtwo χcut;
    let All:=OrdinaryVortexParentProductEvent n qCount D mv (rstar-1) kParent d (Q.length-1) hmParent hd βv ε (α/2) ρ₀
      (ρ₀*(βfreq/200)/2) βP ηP row ηH βH cParent Bparent εTri χhost δref href hpstar P Q π hπ selection p rsv s false R Good;
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) ((rstar-1)+1)→ℝ,
    (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral (rstar-1) (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (weight i) (ρ₀*(βfreq/200)/2) (2*p) rsv
      (2*rsv*(markedVortexInnerHubs Q i).card/(2*p)) βv ξdeep (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom) ∧
    1-(loss+χinner+χdeep+χone+χtwo+χcut)-χhost-χref-χthree≤
      ((μ.sigma ρ).prod (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin))).probability
        (fun z=>All z ∧
          OrdinaryVortexThreeStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D mv βv ε Q π hπ (2*p) rsv s false
            (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
          OrdinaryVortexThreeStepEditedBalanceEvent P D mv βv ε rsv εR εH Qlook π hπ d false
            (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  intro Q
  have hhalf:(n:ℝ)/2≤D:=by
    have hn0:(0:ℝ)≤n:=by positivity
    nlinarith [mul_nonneg (show 0≤θhost-1/2 by linarith) hn0,mul_nonneg hα.le hn0]
  obtain ⟨i₀,rsv,Cres,sampling,w,seed,hwitness,hpoint,hinputs,selection,hprob⟩:=
    ordinary_original_deep_parent_level_witness n qCount D rstar m k d K mv mAbs aAbs bAbs q₀ Nsel Ncorr Nc Ng Nh Ncol Ngeom hd
      βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent ε εabs εv βv ξAbs χlocal χglobal χhub χcol
      BO hsel hgeom hcorr hnsel hngeom hncorr hn hq hmv hρ he F hF habundance hρlo hρhi hthreshold P hreg π hdegree hθ hα hnoshort Q hπ hβv hβv1
      Kdeep v₀ αcut c C a ε₀ ρdeep θdeep aLoad ξdeep b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep hdeep
      hr hβfreq hdeepSize density tR tH kParent Mhost Mcut hmParent βP ηP row ηH βH cParent Bparent εTri χhost δref href χref
      hpstar hselector hcuts hε1 hερ hβα hβε hM hMcut
  refine ⟨i₀,rsv,Cres,sampling,w,seed,hwitness,hpoint,hinputs,selection,?_⟩
  intro R _ ν p p₂ q s μ E loss0 loss Good All
  obtain ⟨weight,hweight,hprior⟩:=hprob ν
  refine ⟨weight,hweight,?_⟩
  let total:=loss+χinner+χdeep+χone+χtwo+χcut+χhost+χref
  have hprior':1-total≤((μ.sigma ν).prod (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin))).probability All:=by
    dsimp [total]; linarith only [hprior]
  have hjoined:=ordinary_assigned_lookback_balance_on_prior_split n qCount D mv m K d mBalance hd
    βfreq ρ₀ θ εR εH βv ε χthree hβfreq hρ hBalanceAt F hF i₀ rsv sampling P hreg (by omega) hhalf hρlo hρhi hmBalance
    Qlook π hπ hnoshort ν (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin)) All total hprior'
  dsimp [total] at hjoined
  linarith only [hjoined]
end Oberwolfach
