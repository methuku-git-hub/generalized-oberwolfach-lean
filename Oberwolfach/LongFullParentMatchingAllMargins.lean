module

public import Oberwolfach.LongFullParentMatching
public import Oberwolfach.LongReferenceHostMargin
public import Oberwolfach.LongAdaptiveVortexDeeperWeightedChosenExtra
public import Oberwolfach.MarkedJointActualEndpointRecordHighProbability
public import Oberwolfach.LongAssignedReferenceLawAlignment
public import Oberwolfach.LongAdaptiveVortexDeeperWeightedExtra
public import Oberwolfach.LongAdaptiveFixedSpacingDeeperExtra
public import Oberwolfach.LongAssignedAdaptiveFixedSpacingCanonicalWithStarts
public import Oberwolfach.MarkedVortexNeighbourhoodConstant
public import Oberwolfach.MarkedVortexNeighbourhoodSizeInputs
public import Oberwolfach.MarkedVortexAdaptiveDegreeInputs
public import Oberwolfach.MarkedFixedVortexSuccessorWeights
public import Oberwolfach.VortexSamplingDomainSizes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_assigned_vortex_matching_full_parent_all_margins
    (r h k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (hγcap:γRich≤αRef)
    (htstar:0<tstar) (htstar1:tstar≤1) (horder:tstar≤sstar) (hkstar:0<kstar)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ ρ₀:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hωBound:4*ω≤ρ₀)
    (ε₀ lam:ℝ) (hε₀:ε₀<1) (hlam:0<lam) (hlamθ:lam≤θ)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (d:ℕ) (hd:2≤d) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ):
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
    let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
    ∀(BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i),
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let hpadded:=@long_padded_seed_length_eq_exponent K
    let pstar₀:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1))))
    let BMseed₀:=2*BM/pstar₀^(2*(r+4)+1)
    let BOseed₀:=fun i=>2*BO i/pstar₀^(2*(ni i+2))
    let Kpair₀:=1+((((r+4):ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i
    let C₀:=10*(((((r+4):ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed₀ i)
    ∃ β βCommon εAbs εRob ζRob δAbs:ℝ,0<β∧0<βCommon∧0<εAbs∧0<εRob∧0<ζRob∧0<δAbs ∧
    ∀ (εRef δRef εQ χ χCommon Qreal pstarRef ζ εBal ζBal χBal εNbr ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel:ℝ)
    (hεRef:0<εRef) (hδRef:0<δRef) (hεQ:0<εQ) (hεQ1:εQ<1/4) (hεQAbs:εQ≤εAbs) (hχ:0<χ)
    (hχCommon:0<χCommon) (hpstarRef:0<pstarRef) (hζ:0<ζ) (hεBal:0<εBal) (hζBal:0<ζBal) (hχBal:0<χBal)
    (hεNbr:0<εNbr) (hζNbr:0<ζNbr) (hχNbr:0<χNbr) (hεLoad:0<εLoad)
    (hζLoad:0<ζLoad) (hχLoad:0<χLoad) (hζLocal:0<ζLocal) (hχLocal:0<χLocal) (hζConfig:0<ζConfig) (hχConfig:0<χConfig) (hτLevel:0<τLevel)
    (hQreal:0<Qreal) (hNbr:ℕ) (hpstarBound:4*(((r+4):ℕ):ℝ)*pstarRef≤ρ₀*(1/100))
    (hgap:χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig<ε₀),
    ∃ εExtra:ℝ,0<εExtra ∧
    ∃ εAbsP ζAbsP δAbsP βconfigP βCommonP:ℝ,
      0<εAbsP ∧ 0<ζAbsP ∧ 0<δAbsP ∧ 0<βconfigP ∧ 0<βCommonP ∧
    ∀ δparent:ℝ,0<δparent→∃βmax:ℝ,0<βmax ∧ ∀βQ:ℝ,0≤βQ→βQ≤1/4→βQ≤αRef/4→βQ≤βmax→βQ≤εBal/4→βQ≤εRef/4→
    ∃MLevel:ℕ,1≤MLevel ∧
    ∃mLevel:ℕ,1≤mLevel ∧ ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧ ∃N:ℕ,
    ∀size:ℕ,∃a₀ b₀ e₀ aRob bRob eRob aParent bParent eParent:ℕ,∀f₀:ℕ,∃NHost:ℕ,
    ∀n:ℕ,∀hn:max (max N NHost) 1≤n,∀(U:Type) [Fintype U] [DecidableEq U],
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (ρ D:ℝ) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (τ A:ℝ) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i))
    (huv:Fintype.card U≤n)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (εHost:ℝ)
    (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C:OrdinaryCycle P (ni i+2),if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤εHost*n)
    (hbudgetV:∀i∈longRetainedSeedIndices F hF K θ,
      6*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+εHost*n≤τ*D)
    (hbudgetE:∀i∈longRetainedSeedIndices F hF K θ,
      5*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ)
    (hτnonneg:0≤τ) (hτbound:τ≤τ₀),
    εHost≤δAbs →
    ∀ (Dnat vsize:ℕ), (Dnat:ℝ)=D → ρ=initialIndexDensity U Dnat →
      P.IsRegularOfDegree Dnat → (1/2+2*αRef)*n≤D → mLevel≤vsize → vsize≤n →
    ∀ (Q:Vortex U P Dnat βQ εQ vsize)
      (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (L:ℕ),L<Q.length →
    kstar≤ρ*(1/100)/2 → kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2 → tstar≤(1/100)/(((r+4):ℕ):ℝ) →
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let Hdom:=Z
    let fV:=markedVortexVertexEmbedding Q
    let gV:=markedVortexHubEmbedding Q
    let ρi:=markedVortexPermutation Q π hpres
    let Aset:=markedVortexInnerVertices Q
    let Bset:=markedVortexInnerHubs Q
    let Scale:=fun i=>Fintype.card (W i)
    let Dbal:=fun i=>2*((Bset i).card:ℝ)/ρ
    let Dlevel:=fun i=>2*(Fintype.card (Z i):ℝ)/ρ
    let bdom:=fun i=>Function.Embedding.refl (Z i)
    let Dload:=Dlevel
    let Aload:=successorWeightLower k₀ ((2*αRef)/4)
    let Bload:=successorWeightUpper k₀ ((2*αRef)/4)
    let AP:∀i,Finset (W i):=fun i=>Finset.univ\markedVortexInnerVertices Q i
    let BP:∀i,Finset (Z i):=fun i=>Finset.univ\markedVortexInnerHubs Q i
    let XP:=fun i=>↥(AP i)
    let fActiveP:=fun i=>markedVortexActiveVertexEmbedding Q i
    let gActiveP:=fun i=>markedVortexActiveHubEmbedding Q i
    let ρActiveP:=fun i=>markedVortexActivePermutation Q π hpres i
    let DactiveP:=fun i=>2*((BP i).card:ℝ)/initialIndexDensity U Dnat
    let pstarLocalP:=ρ₀*sstar/(2*((r+4:ℕ):ℝ))
    let fParentP:=markedVortexVertexEmbedding Q
    let gParentP:=markedVortexHubEmbedding Q
    let gWideP:=markedVortexNonDeeperHubToPhysical Q
    let ρParentP:=markedVortexPermutation Q π hpres
    let DparentP:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U Dnat
    let GP:=P
    let αP:ℝ:=2*αRef
    let Color:=Bool
    let aP:Bool:=false
    let jP:Bool:=false
    let sParent:ℝ:=1/100
    let pParent:=initialIndexDensity U Dnat*sParent/2
    let kParent:=pParent/(((r+4):ℕ):ℝ);
    ∃ weightParentP:∀i,(Fin ((r+4)+1)→W i)→ℝ,
    ∃ weightActiveP:∀i,(Fin ((r+4)+1)→XP i)→ℝ,
    (∀i≤L,SuccessorSequenceWeightConditions (P.comap (fParentP i)) (ρParentP i) (3*d)
      (DparentP i) δparent (successorWeightLower k₀ (αP/4)) (successorWeightUpper k₀ (αP/4)) (weightParentP i)) ∧
    (∀i≤L+1,SuccessorSequenceWeightConditions (P.comap (fActiveP i)) (ρActiveP i) (3*d)
      (DactiveP i) δparent (successorWeightLower k₀ (αP/4)) (successorWeightUpper k₀ (αP/4)) (weightActiveP i)) ∧
    ∃levelWeight:∀i,(Fin ((r+4)+1)→W i)→ℝ,
    (∀i≤L,SuccessorSequenceWeightConditions (P.comap (fV i)) (ρi i) (3*d) (Dload i) τLevel Aload Bload (levelWeight i)) ∧
    let t:=t₀
    let tHub:=ξ*(n:ℝ)
    let b:=longAssignedApproxOrdinaryWeight F hF K (r+4) θ
    let a:=longAssignedApproxMarkedWeight F hF K (r+4) θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/(((r+4):ℕ):ℝ))/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let udens:=2*(∑u,(1-1/100-(1/100)/(((r+4):ℕ):ℝ)-a u-b u))/D
    let q:=longAssignedIntervalProbability F hF K (r+4) θ
    let s:=longAssignedSpokeProbability F hF K (r+4) θ
    let hLaw:=long_assigned_actual_raw_law_parameters (by omega) F hF Allowed hAllowed K (by omega) (r+4) d hm hd θ ρ₀ ρ D
      hθpos.le hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
      d hd q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s
      hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>
      rawExpandedMarkedCollapse e (ω e)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*(r+4)+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let Wm:=longAssignedMarkedSeed F hF K (r+4) d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K (r+4) d θ D P π ni hni w
    let C:=10*(((((r+4):ℕ):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let ℓ:=fun i=>ni i+2
    let Wmix:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d (r+4) ℓ
    let Pair:Option (Fin K)→ℝ:=fun i=>match i with
      | none=>((((r+4):ℕ):ℝ)+1)^4*BMseed
      | some i=>((ni i:ℝ)+2)^3*BOseed i
    let Kpair:=1+((((r+4):ℕ):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed i
    let failure:=4*(Fintype.card U:ℝ)*Real.exp (-2*tHub^2/((4*(d:ℝ)+3)^2*(n:ℝ)))
    letI : Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
    let Eref:=MarkedReferenceActiveAbsorberProperty r h d (αP/2) βconfigP εRef δRef δparent δparent ζAbsP tstar εAbsP
      size aParent bParent eParent f₀ GP Dnat vsize βQ εQ Q π hpres L sParent pParent kParent q s aP jP
    let EParent:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d aP=>
      (∀ i≤L,∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph (W i)) (DS:SimpleGraph (W i⊕Z i)),
        (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
        MarkedPackingLoadsWithSpokes (GP.comap (fParentP i)) (ρParentP i) d (r+4) (DparentP i) pParent kParent sParent (weightParentP i) aP jP
          (Function.Embedding.refl (Z i)) (fun u=>q (gParentP i u)) (fun u=>s (gParentP i u))
          (δparent+δparent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αP/4)/pstarLocalP^(2*(r+4)+1))*δparent+
            33*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αP/4)/pstarLocalP^(2*(r+4)+1))*δ/Fintype.card (W i))
          (rawMarkedDeleteRims (rawMarkedRestrictPair (fParentP i) (gParentP i) z.1) DR.edgeFinset)
          (markedDeletePhysicalSpokes
            (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fParentP i x) (gParentP i u)) DS)) ∧
        (∀ i≤L+1,MarkedLocalSpokeLoadsWithSpokes (GP.comap (fActiveP i)) (ρActiveP i) d (r+4) (DactiveP i) pParent kParent sParent (weightActiveP i)
        (δparent+δparent+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αP/4)/pstarLocalP^(2*(r+4)+1))*δparent)
        (rawMarkedRestrictPair (fActiveP i) (gActiveP i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fActiveP i x) (gActiveP i u))) ∧ Eref z;
    let fCut:=fun i=>markedVortexVertexEmbedding Q (i+1)
    let gCut:=fun i=>markedVortexHubEmbedding Q (i+1)
    let ρCut:=fun i=>markedVortexPermutation Q π hpres (i+1)
    let ECut:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d aP=>∀ i≤L,
      MarkedCutFamiliesWithSpokes (GP.comap (fCut i)) (ρCut i) d (αP/2) pParent kParent tstar δparent
        (rawMarkedRestrictPair (fCut i) (gCut i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fCut i x) (gCut i u));
    let EConfig:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d aP=>∀ i≤L,
      MarkedLocalConfigurationsWithSpokes r (GP.comap (fParentP i)) (ρParentP i) d Finset.univ
        (markedLocalCycleCoefficient r (αP/2) (tstar/2) kstar-(r+5:ℕ)*δparent)
        (markedLocalPathCoefficient r (αP/2) (tstar/2) kstar-(r+4:ℕ)*δparent)
        (rawMarkedRestrictPair (fParentP i) (gParentP i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fParentP i x) (gParentP i u));
    let EActive:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d aP=>∀ i≤L,
      MarkedLocalConfigurationsWithSpokes r (GP.comap (fActiveP (i+1))) (ρActiveP (i+1)) d Finset.univ
        (markedLocalCycleCoefficient r (αP/2) (tstar/2) kstar-(r+5:ℕ)*δparent)
        (markedLocalPathCoefficient r (αP/2) (tstar/2) kstar-(r+4:ℕ)*δparent)
        (rawMarkedRestrictPair (fActiveP (i+1)) (gParentP i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fActiveP (i+1) x) (gParentP i u));
    let EWide:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d aP=>∀ i≤L,
      MarkedLocalSpokeLoadsWithSpokes (GP.comap (fActiveP (i+1))) (ρActiveP (i+1)) d (r+4) (DactiveP (i+1)) pParent kParent sParent (weightActiveP (i+1))
        (δparent+δparent+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αP/4)/pstarLocalP^(2*(r+4)+1))*(4/εQ)*δparent)
        (rawMarkedRestrictPair (fActiveP (i+1)) (gWideP i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fActiveP (i+1) x) (gWideP i u));
    let ERow:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d aP=>∀ i≤L,
      MarkedRowsWithSpokes (GP.comap (fActiveP (i+1))) (ρActiveP (i+1)) d 1 Finset.univ pParent kParent
        (fun u=>q (gWideP i u)) (fun u=>s (gWideP i u)) aP jP ((δparent+δparent)*Fintype.card (XP (i+1)))
        (rawMarkedRestrictPair (fActiveP (i+1)) (gWideP i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fActiveP (i+1) x) (gWideP i u));
    let ECommon:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d aP=>∀ i≤L,
      MarkedCommonConfigurationsWithSpokes r (GP.comap (fParentP i)) (ρParentP i) d βCommonP δparent
        (rawMarkedRestrictPair (fParentP i) (gParentP i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fParentP i x) (gParentP i u));
    let EFull:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d aP=>∀ i≤L,
      MarkedRowsWithSpokes (GP.comap (fParentP i)) (ρParentP i) d (r+12) Finset.univ pParent kParent
        (fun u=>q (gParentP i u)) (fun u=>s (gParentP i u)) aP jP
        ((δparent+(r+12:ℕ)*δparent)*Fintype.card (W i))
        (rawMarkedRestrictPair (fParentP i) (gParentP i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fParentP i x) (gParentP i u)) ∧
      MarkedIndicesWithSpokes (ρParentP i) d (r+12) Finset.univ
        (fun u=>q (gParentP i u)) (fun u=>s (gParentP i u)) aP jP
        ((δparent+(r+12:ℕ)*δparent)*Fintype.card (Z i))
        (rawMarkedRestrictPair (fParentP i) (gParentP i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fParentP i x) (gParentP i u));
    let EAgreement:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d aP=>∀ i≤L,
      let ω:=rawMarkedRestrictPair (fParentP i) (gParentP i) z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fParentP i x) (gParentP i u);
      (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes (ρParentP i) d ω aP jP b x u↔H b x u) then (1:ℝ) else 0)≤δparent*Fintype.card (Z i)) ∧
      (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes (ρParentP i) d ω aP jP b x u↔H b x u) then (1:ℝ) else 0)≤δparent*Fintype.card (W i));
    let EActualCuts:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d aP=>∀ i≤L,
      MarkedReferenceCutFamilies (GP.comap (fParentP i)) (ρParentP i) d aP jP (αP/8) pParent kParent
        (sParent/((r+4:ℕ):ℝ)) (rawMarkedRestrictPair (fParentP i) (gParentP i) z.1);
    let ParentGood:=(fun z=>MarkedActualVortexBalanceProperty Q π hpres d (r+4) L aP jP εBal ζBal
        (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) z ∧
      (L=0 ∨ MarkedActualVortexBalanceProperty Q π hpres d (r+4) (L-1) aP jP εBal ζBal
        (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z) ∧ EActualCuts z ∧ EAgreement z ∧ EFull z ∧ ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z ∧
      (∀ βA βrec κ:ℝ, βA≤βCommonP → δparent≤κ/4 →
        3*βA≤markedLocalCycleCoefficient r (αP/2) (tstar/2) kstar-(r+5:ℕ)*δparent →
        3*βA≤markedLocalPathCoefficient r (αP/2) (tstar/2) kstar-(r+4:ℕ)*δparent →
        βrec≤βA → δparent+(r+12:ℕ)*δparent≤κ/4 → δparent≤κ/4 → εRef=κ/4 → δRef=κ →
        ∀ thetaDeep:ℝ,
        δparent+δparent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αP/4)/pstarLocalP^(2*(r+4)+1))*δparent≤κ/4 →
        δparent+δparent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αP/4)/pstarLocalP^(2*(r+4)+1))*δparent≤thetaDeep/4 →
        ∀ etaBal x:ℝ,0≤x → εBal+((r+4)+2:ℕ)*ζBal≤etaBal →
        εBal+((r+4)+2:ℕ)*ζBal≤x/2 → L+1=Q.length →
        ∀ eta:ℝ, δparent+δparent≤(sParent/((r+4:ℕ):ℝ))/8 →
        δparent+δparent+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αP/4)/pstarLocalP^(2*(r+4)+1))*(4/εQ)*δparent≤eta/4 →
        ∀ deltaI hIcut:ℝ, βQ≤1/4 → 0≤hIcut → deltaI≤(αP/2)/32 → deltaI≤kstar/32 →
        2*deltaI≤tstar/8 → 2*hIcut≤(αP/2)*kstar/4 → 2*hIcut≤tstar/8-δparent →
        δparent+h*δparent≤x/2 →
    (∀ i≤L,
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let fActiveP:=markedVortexNextActiveInNonDeeper Q i
      let gA:markedVortexNonDeeperHubType Q i→markedVortexHubType Q i:=Subtype.val
      let ρP:=markedVortexPermutation Q π hpres i
      let ρActiveP:=markedVortexActivePermutation Q π hpres (i+1)
      let σP:=rawMarkedRestrictPair fP gP z.1
      let HP:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fP x) (gP u);
      MarkedCommonConfigurationsWithSpokes r (GP.comap fP) ρP d βA (κ/4) σP HP ∧
      MarkedLocalConfigurationsWithSpokes r (GP.comap fP) ρP d Finset.univ
        (3*(min βA ((sParent/((r+4:ℕ):ℝ))/4))) (3*(min βA ((sParent/((r+4:ℕ):ℝ))/4))) σP HP ∧
      MarkedLocalConfigurationsWithSpokes r ((GP.comap fP).comap (fun x=>fA (fActiveP x))) ρActiveP d Finset.univ
        (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (fActiveP x)) gA σP)
        (fun b x u=>HP b (fA (fActiveP x)) (gA u))) ∧
    (∀ i≤L,
      let W:=markedVortexVertexType Q i; let Z:=markedVortexHubType Q i
      let fActiveP:=markedVortexVertexEmbedding Q i; let gActiveP:=markedVortexHubEmbedding Q i
      let ρActiveP:=markedVortexPermutation Q π hpres i; let σ:=rawMarkedRestrictPair fActiveP gActiveP z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fActiveP x) (gActiveP u);
      MarkedRowsWithSpokes (GP.comap fActiveP) ρActiveP d (r+12) Finset.univ pParent kParent (fun u=>q (gActiveP u)) (fun u=>s (gActiveP u)) aP jP ((κ/4)*Fintype.card W) σ H ∧
      MarkedIndicesWithSpokes ρActiveP d (r+12) Finset.univ (fun u=>q (gActiveP u)) (fun u=>s (gActiveP u)) aP jP ((κ/4)*Fintype.card W) σ H ∧
      (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes ρActiveP d σ aP jP b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card Z) ∧
      (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes ρActiveP d σ aP jP b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card W)) ∧
    (∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let fActiveP:=markedVortexVertexEmbedding Q i
      let gActiveP:=markedVortexHubEmbedding Q i
      let ρActiveP:=markedVortexPermutation Q π hpres i
      let rho:=initialIndexDensity U Dnat
      let c:ℝ:=(r+4:ℕ)
      let t:=sParent/c
      let pRef:=rho*c*t/2
      let kRef:=pRef/c
      let DRef:=2*(Fintype.card Z:ℝ)/rho
      let σ:=rawMarkedRestrictPair fActiveP gActiveP z.1;
      MarkedReferenceStatistics (GP.comap fActiveP) ρActiveP d aP jP DRef (κ/4) κ (2*(αP/16)) pRef kRef (c*t) t σ ∧
      MarkedReferenceCutFamilies (GP.comap fActiveP) ρActiveP d aP jP (2*(αP/16)) pRef kRef t σ) ∧
    (∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let P:=GP.comap (markedVortexVertexEmbedding Q i)
      let ρActiveP:=markedVortexPermutation Q π hpres i
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U Dnat
      let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b
        (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)
      let qi:=fun u=>q (markedVortexHubEmbedding Q i u)
      let si:=fun u=>s (markedVortexHubEmbedding Q i u);
      MarkedLocalSpokeLoadsWithSpokes P ρActiveP d (r+4) Dload pParent kParent sParent (weightParentP i) (thetaDeep/4) σ H ∧
      (let seed:=fun XP:MarkedWheel (Prod.fst:W×W→W) Prod.snd Prod.fst Prod.snd (r+4) ρActiveP (3*d)
          (fun (_:W) (_:Z)=>True) (fun _ _=>True)=>weightParentP i XP.1.val/(Dload*pParent^(r+4)*kParent*sParent^(r+4));
        ∀ root:((W×W)⊕(W×W))⊕(Bool×W×Z),
          rawMarkedWheelMarginal P ρActiveP d pParent kParent qi si aP jP root≠0→
          |typedMarkedPotentialLoad seed (rawMarkedPairRims P ρActiveP d σ) H root-1|≤κ/4)) ∧
    (∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let fActiveP:=markedVortexVertexEmbedding Q i
      let gActiveP:=markedVortexHubEmbedding Q i
      let ρActiveP:=markedVortexPermutation Q π hpres i
      let σ:=rawMarkedRestrictPair fActiveP gActiveP z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fActiveP x) (gActiveP u)
      let E:=MarkedSampleArc (GP.comap fActiveP) ρActiveP (3*d) (fun e=>σ (Sum.inl e)) false
      let K:=MarkedSampleArc (GP.comap fActiveP) ρActiveP (3*d) (fun e=>σ (Sum.inl e)) true
      let S:=Finset.univ.filter (fun s:W×Z=>H false s.1 s.2∨H true s.1 s.2)
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      let T:=markedVortexDeeperVertices Q i
      let R:=markedVortexDeeperHubs Q i
      let bal:=markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S (r+4);
      ∃ errInner errDeep:ℝ, 0≤errDeep ∧
      errInner≤(x/2)*Fintype.card W ∧ errDeep≤(x/2)*Fintype.card W ∧
      (∀ v jP,|bal I J v jP|≤errInner) ∧
      (∀ v jP,|bal T R v jP|≤errDeep) ∧
      (∀ v jP,|bal I J v jP|≤etaBal*I.card)) ∧
    (∀ i≤L,
      let Z:=markedVortexHubType Q i
      let Zkeep:=markedVortexNonDeeperHubType Q i
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let fActiveP:=markedVortexNextActiveInNonDeeper Q i
      let gA:Zkeep→Z:=Subtype.val
      let ρActiveP:=markedVortexActivePermutation Q π hpres (i+1)
      let σP:=rawMarkedRestrictPair fP gP z.1
      let HP:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fP x) (gP u);
      MarkedRowsWithSpokes ((GP.comap fP).comap (fun x=>fA (fActiveP x))) ρActiveP d 1 Finset.univ pParent kParent
        (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) aP jP
        (((sParent/((r+4:ℕ):ℝ))/8)*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))))
        (rawMarkedRestrictPair (fun x=>fA (fActiveP x)) gA σP) (fun b x u=>HP b (fA (fActiveP x)) (gA u)) ∧
      MarkedLocalSpokeLoadsWithSpokes ((GP.comap fP).comap (fun x=>fA (fActiveP x))) ρActiveP d (r+4) (DactiveP (i+1)) pParent kParent sParent (weightActiveP (i+1)) (eta/4)
        (rawMarkedRestrictPair (fun x=>fA (fActiveP x)) gA σP) (fun b x u=>HP b (fA (fActiveP x)) (gA u))) ∧
    (∀ i≤L,
    (∀ mark,BipartiteLargeCut
      (fun x:↥(markedVortexInnerVertices Q i)=>fun y:↥(markedVortexInnerVertices Q i)=>
        markedPhysicalRim (GP.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) (3*d)
          (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1 (Sum.inl e)) mark x.val y.val) deltaI (2*hIcut)) ∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (fun x:↥(markedVortexInnerVertices Q i)=>fun u:↥(markedVortexInnerHubs Q i)=>
      retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP mark
        (markedVortexVertexEmbedding Q i x.val) (markedVortexHubEmbedding Q i u.val))) deltaI (2*hIcut))) ∧
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let ρActiveP:=markedVortexPermutation Q π hpres i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let fActiveP:=markedVortexNextActiveInNonDeeper Q i
      let gA:=markedVortexNonDeeperHubToParent Q i
      let XP:=Finset.univ.image fActiveP
      let Zinner:=markedVortexInnerNonDeeperHubs Q i
      let ω:=rawMarkedRestrictPair fP gP z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) aP
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) aP)) z.2 aP jP b (fP x) (gP u);
      ∃ errR errI:ℝ,0≤errR ∧ 0≤errI ∧ errR≤(x/2)*Fintype.card W ∧ errI≤(x/2)*Fintype.card W ∧
        MarkedRowsWithSpokes (GP.comap fP) ρActiveP d h (XP.image fA) pParent kParent (fun u=>q (gP u)) (fun u=>s (gP u)) aP jP errR ω H ∧
        MarkedIndicesWithSpokes ρActiveP d h (Zinner.image gA) (fun u=>q (gP u)) (fun u=>s (gP u)) aP jP errI ω H));
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      startRetentionLaw (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let Prior:=MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γRich p₁ k₁ (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
      P π fV gV ρi Aset Bset Scale Dlevel Dload bdom levelWeight q s false false;
    ∃z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω)),
      0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ Prior ⟨f z.1,z.2⟩ ∧ ParentGood ⟨f z.1,z.2⟩ ∧
        (Q.length-1=0 ∨ MarkedActualVortexBalanceProperty Q π hpres d (r+4) ((Q.length-1)-1) false false εBal ζBal
          (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) ⟨f z.1,z.2⟩) ∧
        (∀u i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*
          (1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p₁^2-(n:ℝ)^(3/4:ℝ)-
          2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
            0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
            0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)) ∧
        (∀u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(n:ℝ)*q u g/d|<(n:ℝ)^(3/4:ℝ)/d) ∧
        MarkedRetainedReservoirSelection r d size a₀ b₀ e₀ f₀ εAbs P π false false ⟨f z.1,z.2⟩ ∧
        MarkedVortexFixedSelection r d size a₀ b₀ e₀ f₀ εAbs P π false false ⟨f z.1,z.2⟩ ∧
        (∀b u,|rawMarkedRestrictedSpokeCol π d (fun e=>z.1 (Sum.inr e)) true true b u Finset.univ-
          (if b then q u true else s u true)*(n:ℝ)|<tHub) ∧
        (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun root=>
          longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true)).card:ℝ)-
          longAssignedApproxOrdinaryWeight F hF K (r+4) θ u*n|≤tHub) ∧
        rawMarkedSeedConcentrated P π d (r+4) p₂ k₂ q s true true t Wm
          (fun e=>rawExpandedApproximateCollapse e (z.1 e)) ∧
        (∀i,rawOrdinarySeedConcentrated P π d (ni i+2) p₂ k₂ q s true true t (Wo i)
          (fun e=>rawExpandedApproximateCollapse e (z.1 e))) ∧
        (∀i root,longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true→
          |resourcePatternLoad (longRawHubResources (U:=U) π d (r+4) (fun i=>ni i+2) i)
            (longMixedSeedWeight Wm Wo i) (fun _ _=>true) root
            (longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true)-
            longAssignedMixedTarget F hF K (r+4) θ D p₂ k₂ i root|≤
          t+τ*longAssignedMixedTarget F hF K (r+4) θ D p₂ k₂ i root) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let e:{v // v∈S}↪_:=Function.Embedding.subtype _
          ∀ztest:LongRetainedHubTest F hF K θ,
            θ*(n:ℝ)/(200*(K:ℝ)*(K:ℝ))≤
              ∑c:RestrictedResource (mixedCandidateResources R) e,
                longRetainedHubIndicator F hF θ hub ztest c.val*mixedCandidateWeight Wmix c.val) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→0≤t+C*(δ/(n:ℝ))+4*τ ∧ t+C*(δ/(n:ℝ))+4*τ≤eps/2) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
          let e:S↪LongRawHubResource n U:=Function.Embedding.subtype _
          let Cand:=RestrictedResource (mixedCandidateResources R) e
          let Q:=restrictedResourceSet (mixedCandidateResources R) e
          let fS:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
          let φ:=fS.trans (markedRawSampledPhysicalEmbedding P π d raw true true)
          let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
          let test:=fun (j:LongRetainedHubTest F hF K θ) (c:Cand)=>longRetainedHubIndicator F hF θ hub j c.val
          ∃M:Finset Cand,(∀c∈M,0<mixedCandidateWeight Wmix c.val) ∧
            (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
            (∀x,alpha*n≤(rimIncidentResources φ x).card →
              ((rimIncidentResources φ x\M.biUnion Q).card:ℝ)≤γ*(rimIncidentResources φ x).card) ∧
            (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (alpha*n) (γ*(longRawIncidenceSet S i).card)) ∧
            (∀i,alpha*n≤(longRawIncidenceSet S i).card →
              ((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤γ*(longRawIncidenceSet S i).card) ∧
            (∀j,(1-γ)*(∑c,test j c*mixedCandidateWeight Wmix c.val)≤∑c∈M,test j c) ∧
            (∀j,(∑c∈M,test j c)≤(1+γ)*(∑c,test j c*mixedCandidateWeight Wmix c.val)) ∧
            (∀x,((physicalRimResidualGraph (markedRawSampledPhysicalEmbedding P π d raw true true)
              ((M.map (survivingCandidateEmbedding (mixedCandidateResources R) S T
                (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset))).biUnion
                (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤max alpha γ*n+δ) ∧
            let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
            let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
            ∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U),
            MarkedFixedTerminalAbsorber P π d (r+4) selected H Reserve X Z →
            let state:=longRawHubState P π d raw true true
    let T:=bernoulliVertexSet state
    let eraw:{z // z∈T}↪_:=Function.Embedding.subtype _
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let N:=M.map q
    let A:=LongRawSelectedOrdinary π d (r+4) ℓ eraw N
    let Q:=longRawSelectedOrdinaryWheel π d (r+4) ℓ eraw N
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
    (∀u,Fintype.card (longRawSourceDomain F π d (r+4) ℓ eraw N C u) =
      ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d (r+4) ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u} =
      n - ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d (r+4) ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,|((Fintype.card (longRawSourceDomain F π d (r+4) ℓ eraw N C u):ℕ):ℝ) -
      (1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u,|((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) -
      ((n:ℝ)-(1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u))| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u, (n:ℝ)*ordinaryAssignedFraction F hF K u none -
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ)) ≤
        ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) ∧
      ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) ≤
        (n:ℝ)*(ordinaryAssignedFraction F hF K u none+(101/100:ℝ)*θ) +
          ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u v,K<Fintype.card ((F u).connectedComponentMk v)→
      v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u) ∧
    let T:=longRawSourceDomain F π d (r+4) ℓ eraw N C
    ∃ψ:∀u,(T u)↪Fin n,
      (∀u x y,(F u).Adj x.val y.val→
        rawMarkedPairRims P π d raw (Sum.inl (ψ u x,ψ u y)) ∨
        rawMarkedPairRims P π d raw (Sum.inl (ψ u y,ψ u x))) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdges (T u) ((F u).induce (T u)) (ψ u))
        (partialFactorPhysicalEdges (T v) ((F v).induce (T v)) (ψ v))) ∧
      (∀u x y,(F u).Adj x.val y.val→Sum.inl ({ψ u x,ψ u y}:Finset (Fin n))∉Reserve) ∧
      (∀u x y,(F u).Adj x.val y.val→s(ψ u x,ψ u y)∉Del.edgeFinset)) := by
  by_cases hαCap:2*αRef≤1
  · exact long_assigned_vortex_matching_with_full_parent_event r h k₀ Qpow hr hQpow hlen αRef sstar ω γRich tstar kstar
      hαRef hsstar hsstar1 hω hmargin hαCap hγRich hγRich1 hγcap htstar htstar1 horder hkstar
      K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ htstarBound d hd hcut
  · obtain ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,hW⟩:=
      long_assigned_adaptive_vortex_deeper_weighted_with_chosen_extra r k₀ Qpow hr hQpow hlen αRef sstar ω γRich tstar kstar
        hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap htstar htstar1 horder hkstar
        K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ htstarBound d hd hcut
    refine ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,?_⟩
    intro BM hBM BO hBO ni hni hpadded pstar₀ BMseed₀ BOseed₀ Kpair₀ C₀
    obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,hW⟩:=hW BM hBM BO hBO
    refine ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,?_⟩
    intro εRef δRef εQ χ χCommon Qreal pstarRef ζ εBal ζBal χBal εNbr ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel
      hεRef hδRef hεQ hεQ1 hεQAbs hχ hχCommon hpstarRef hζ hεBal hζBal hχBal hεNbr hζNbr hχNbr hεLoad hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hτLevel hQreal hNbr hpstarBound hgap
    obtain ⟨εExtra,hεExtra,βmax,hβmax,hW⟩:=hW εRef δRef εQ χ χCommon Qreal pstarRef ζ εBal ζBal χBal εNbr ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel
      hεRef hδRef hεQ hεQ1 hεQAbs hχ hχCommon hpstarRef hζ hεBal hζBal hχBal hεNbr hζNbr hχNbr hεLoad hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hτLevel hQreal hNbr hpstarBound hgap
    refine ⟨εExtra,hεExtra,1,1,1,1,1,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
    intro δparent hδparent
    refine ⟨βmax,hβmax,?_⟩
    intro βQ hβQ hβQ1 hβQα hβQmax hβQbal hβQref
    obtain ⟨MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,N,hW⟩:=
      hW βQ hβQ hβQ1 hβQα hβQmax hβQbal hβQref
    refine ⟨MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,N,?_⟩
    intro size
    obtain ⟨a₀,b₀,e₀,aRob,bRob,eRob,hW⟩:=hW size
    refine ⟨a₀,b₀,e₀,aRob,bRob,eRob,0,0,0,?_⟩
    intro f₀
    obtain ⟨NHost,hW⟩:=hW f₀
    refine ⟨NHost,?_⟩
    intro n hn U _ _ F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort εHost he hdeg hbudgetV hbudgetE hτnonneg hτbound hεHostAbs
    intro Dnat vsize hDeq hρeq hreg hDmin
    have hnpos:0<Fintype.card (Fin n):=by simp only [Fintype.card_fin];omega
    have hDmin':(1/2+2*αRef)*Fintype.card (Fin n)≤(Dnat:ℝ):=by simpa only [Fintype.card_fin,hDeq] using hDmin
    have hh:=long_reference_host_margin_le_half P Dnat (2*αRef) hreg hnpos hDmin'
    exfalso
    linarith
end Oberwolfach
