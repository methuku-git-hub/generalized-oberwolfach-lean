module

public import Oberwolfach.LongAssignedAdaptiveSpacingInnerColumnRimRow
public import Oberwolfach.LongAssignedAdaptiveSpacingInnerColumn
public import Oberwolfach.LongAssignedAdaptiveFixedSpacingPathTests
public import Oberwolfach.LongAssignedAdaptiveFixedSpacingNeighbourTests
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

theorem long_assigned_adaptive_fixed_spacing_weighted_with_inner_column_and_rim_row
    (r k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (hγcap:γRich≤αRef)
    (htstar:0<tstar) (htstar1:tstar≤1) (horder:tstar≤sstar) (hkstar:0<kstar)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ ρ₀:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hωBound:4*ω≤ρ₀)
    (ζret:ℝ) (hζret:0<ζret)
    (ε₀ lam:ℝ) (hε₀:ε₀<1) (hlam:0<lam) (hlamθ:lam≤θ)
    (d:ℕ) (hd:2≤d) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ) (hspace:1/(8*(d:ℝ))≤θ/2):
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
    ∃βmax:ℝ,0<βmax ∧ ∀βQ:ℝ,0≤βQ→βQ≤1/4→βQ≤αRef/4→βQ≤βmax→βQ≤εBal/4→βQ≤εRef/4→
    ∃MLevel:ℕ,1≤MLevel ∧
    ∃mLevel:ℕ,1≤mLevel ∧ ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧ ∃N:ℕ,
    ∀size:ℕ,∃a₀ b₀ e₀ aRob bRob eRob:ℕ,∀f₀:ℕ,∃NHost:ℕ,
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
    (vertices:Finset (Fin n)) (εHost:ℝ)
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
      P.IsRegularOfDegree Dnat → (1/2+2*αRef)*n≤D → mLevel≤vsize →
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
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      startRetentionLaw (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let Prior:=MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γRich p₁ k₁ (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
      P π fV gV ρi Aset Bset Scale Dlevel Dload bdom levelWeight q s false false
    ∃z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω)),
      0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ Prior ⟨f z.1,z.2⟩ ∧
        (∀x,|(((P.neighborFinset x∩vertices).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
          udens*(P.neighborFinset x∩vertices).card|<(n:ℝ)^(3/4:ℝ)) ∧
        RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
          (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret z.2 ∧
        (∀u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u vertices-
          (vertices.card:ℝ)*(1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Finset.univ-
          ∑u:U,(1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀x y,x≠y→((5/32:ℝ)*θ^2-1/(4*(d:ℝ)))*Fintype.card U-5*(n:ℝ)^(3/4:ℝ)≤
          (rawProtectedPairHubs π d (fun e=>z.1 (Sum.inr e)) false true
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 x y).card) ∧
        (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
          4*(Fintype.card U:ℝ)/(((r+4):ℕ):ℝ)+4*(n:ℝ)^(3/4:ℝ)) ∧
        (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
          (((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (x,u)=some (Sum.inr false) ∧
            rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (y,u)=some (Sum.inr false))).card:ℝ)) ∧
        (∀u i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*
          (1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) u false
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*s u false|<(n:ℝ)^(3/4:ℝ)) ∧
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
      (∀u x y,(F u).Adj x.val y.val→s(ψ u x,ψ u y)∉Del.edgeFinset)) :=by
  obtain ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,hOuter⟩:=
    long_assigned_adaptive_fixed_spacing_canonical_with_inner_column_and_rim_row r k₀ Qpow hr hQpow hlen αRef sstar ω γRich tstar kstar (ρ₀/8)
      hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 htstar htstar1 horder hkstar (by positivity)
      K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret hζret ε₀ lam hε₀ hlam hlamθ d hd hcut hspace
  refine ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,?_⟩
  intro BM hBM BO hBO ni hni hpadded pstar₀ BMseed₀ BOseed₀ Kpair₀ C₀
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,hLate⟩:=hOuter BM hBM BO hBO
  refine ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,?_⟩
  intro εRef δRef εQ χ χCommon Qreal pstarRef ζ εBal ζBal χBal εNbr ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel
    hεRef hδRef hεQ hεQ1 hεQAbs hχ hχCommon hpstarRef hζ hεBal hζBal hχBal hεNbr hζNbr hχNbr hεLoad hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hτLevel hQreal hNbr hpstarBound hgap
  obtain ⟨Knbr,hKnbr,hKI,hKJ⟩:=marked_vortex_neighbourhood_constant_exists εQ ρ₀ hεQ hρ₀
  have hα:0<2*αRef:=by positivity
  have hmargin':successorCycleRatio k₀+(2*αRef)/4≤1/2+(2*αRef)/2:=by linarith only [hmargin]
  obtain ⟨βmax,hβmax,hweights⟩:=marked_fixed_vortex_successor_weight_families k₀ (r+4) hlen (2*αRef) τLevel hα hτLevel hmargin'
  refine ⟨βmax,hβmax,?_⟩
  intro βQ hβQ hβQ1 hβQα hβQmax hβQbal hβQref
  let Bload:=successorWeightUpper k₀ ((2*αRef)/4)
  have hBload:0<Bload:=(successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2
  obtain ⟨MLevel,hMLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,N,hAll⟩:=
    hLate εRef δRef εQ χ χCommon 1 Qreal pstarRef ζ εBal 1 ζBal χBal εNbr Knbr ζNbr χNbr Bload εLoad 1 ζLoad χLoad ζLocal χLocal ζConfig χConfig
      hεRef hδRef hεQ (by linarith) hχ hχCommon hpstarRef hζ hεBal (by norm_num) hζBal hχBal hεNbr hKnbr hζNbr hχNbr hBload hεLoad (by norm_num) hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hQreal hNbr hpstarBound hgap
  obtain ⟨mGeom,hmGeom,hGeom⟩:=marked_fixed_vortex_baseline_geometry βQ εQ ρ₀ hβQ hβQ1 hεQ hεQ1 hρ₀ MLevel
  obtain ⟨Nw,hNw,hweights⟩:=hweights (3*d)
  let mLevel:=max mGeom ⌈2*(Nw:ℝ)/εQ⌉₊
  refine ⟨MLevel,hMLevel,mLevel,by dsimp [mLevel];omega,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,N,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,aRob,bRob,eRob,hAll⟩:=hAll size
  refine ⟨a₀,b₀,e₀,aRob,bRob,eRob,?_⟩
  intro f₀
  obtain ⟨NHost,hAll⟩:=hAll f₀
  refine ⟨NHost,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort vertices εHost he hdeg hbudgetV hbudgetE hτnonneg hτbound hεHostAbs
  intro Dnat vsize hDeq hρeq hreg hDmin hmLevel Q hpres L hL hpstar0 hkstar0 htstar0 W Z Hdom fV gV ρi Aset Bset Scale Dbal Dlevel bdom Dload Aload Bload'
  have hnpos:0<n:=by omega
  letI : Nonempty (Fin n):=⟨⟨0,hnpos⟩⟩
  have hDmin':(1/2+2*αRef)*Fintype.card (Fin n)≤(Dnat:ℝ):=by simpa [hDeq] using hDmin
  have hDhalf:(Fintype.card (Fin n):ℝ)/2≤(Dnat:ℝ):=by
    have hn0:(0:ℝ)≤Fintype.card (Fin n):=Nat.cast_nonneg _
    nlinarith [mul_nonneg hαRef.le hn0]
  have hρlo':ρ₀ ≤ initialIndexDensity U Dnat:=by simpa [hρeq] using hρlo
  have hρhi':initialIndexDensity U Dnat≤1:=by simpa [hρeq] using hρ1
  have hρpos:0 < initialIndexDensity U Dnat:=hρ₀.trans_le hρlo'
  have hmGeom':mGeom≤vsize:=(le_max_left _ _).trans hmLevel
  have hmpos:0<vsize:=by omega
  have hceil:2*(Nw:ℝ)/εQ≤vsize:=(Nat.le_ceil _).trans (by exact_mod_cast (show ⌈2*(Nw:ℝ)/εQ⌉₊≤vsize from (le_max_right _ _).trans hmLevel))
  have hweightSize:(Nw:ℝ)≤εQ*vsize/2:=by
    have hh:2*(Nw:ℝ)≤(vsize:ℝ)*εQ:=(div_le_iff₀ hεQ).mp hceil
    nlinarith
  obtain ⟨levelWeight,hWeight⟩:=hweights (Fin n) U P Dnat vsize βQ εQ Q hreg (by simpa using hnpos) hDmin' hρpos hβQ hβQmax hεQ hweightSize π hpres L hL
  have hGeometry:=hGeom (Fin n) U P Dnat vsize hreg (by simpa using hnpos) hDhalf hρlo' hρhi' hmGeom' Q π hpres L hL
  have hSizes:=marked_vortex_neighbourhood_size_inputs Q hreg (by simpa using hnpos) hDhalf hρ₀ hρlo' hρhi' hβQ hβQ1 hεQ (by linarith) hmpos Knbr (by linarith) hKI hKJ L hL
  have hDegrees:=marked_vortex_adaptive_degree_inputs Q hreg (by simpa using hnpos) hDmin' hα hρpos hβQ (by linarith) hβQ1 hεQ hmpos γRich βQ βQ hγRich.le (by linarith) le_rfl le_rfl L hL
  have hLength:=Q.number_of_levels_le_order hεQ (by linarith) hmpos
  have hLsize:(L+1:ℝ)≤(Fintype.card (Fin n):ℝ)^((1:ℝ)):=by
    rw [Real.rpow_one]
    exact_mod_cast (show L+1≤Fintype.card (Fin n) by omega)
  have hmind:∀v,(1/2+αRef)*n≤(P.degree v:ℝ):=by
    intro v
    rw [hreg v]
    have hn0:(0:ℝ)≤n:=Nat.cast_nonneg _
    nlinarith [mul_nonneg hαRef.le hn0]
  have hWsize:∀i≤L,MLevel≤Fintype.card (W i):=fun i hi=>(hGeometry.2 i hi).2.2.1
  have hZsize:∀i≤L,MLevel≤Fintype.card (Z i):=fun i hi=>(hGeometry.2 i hi).2.2.2.1
  have hWstep:∀i<L,(Fintype.card (W (i+1)):ℝ)≤εQ*Fintype.card (W i):=fun i hi=>(hGeometry.2 i (by omega)).2.2.2.2.2.2.2.2.1
  have hZlo:∀i≤L,(ρ₀/8)*(Fintype.card (W i):ℝ)≤Fintype.card (Z i):=fun i hi=>(hGeometry.2 i hi).2.2.2.2.1
  have hZhi:∀i≤L,Fintype.card (Z i)≤Fintype.card (W i):=fun i hi=>(hGeometry.2 i hi).2.2.2.2.2.1
  have hZW:∀i≤L,(Fintype.card (Z i):ℝ)≤(1:ℝ)*Fintype.card (W i):=by
    intro i hi
    have hh:(Fintype.card (Z i):ℝ)≤Fintype.card (W i):=by exact_mod_cast hZhi i hi
    simpa using hh
  have hIsize:∀i≤L,MLevel≤(Aset i).card:=fun i hi=>(hGeometry.2 i hi).1
  have hJsize:∀i≤L,MLevel≤(Bset i).card:=fun i hi=>(hGeometry.2 i hi).2.1
  have hScale:∀i<L,(Scale (i+1):ℝ)≤εQ*Scale i:=by simpa [Scale] using hWstep
  have hAS:∀i≤L,(Aset i).card≤Scale i:=fun i hi=>(hGeometry.2 i hi).2.2.2.2.2.2.1
  have hBS:∀i≤L,(Bset i).card≤Scale i:=fun i hi=>(hGeometry.2 i hi).2.2.2.2.2.2.2.1
  have hInv:∀i≤L,∀x,ρi i x∈Aset i↔x∈Aset i:=fun i hi=>(hGeometry.2 i hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hWS:∀i≤L,(Fintype.card (W i):ℝ)≤(1:ℝ)*Scale i:=by intro i hi; simp [Scale]
  have hZS:∀i≤L,(Fintype.card (Z i):ℝ)≤(1:ℝ)*Scale i:=by simpa [Scale] using hZW
  have hIstep:∀i<L,((Aset (i+1)).card:ℝ)≤εQ*(Aset i).card:=fun i hi=>(hGeometry.2 i (by omega)).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hJstep:∀i<L,((Bset (i+1)).card:ℝ)≤εQ*(Bset i).card:=fun i hi=>(hGeometry.2 i (by omega)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hWI:∀i≤L,(Fintype.card (W i):ℝ)≤Knbr*(Aset i).card:=fun i hi=>(hSizes i hi).1
  have hZI:∀i≤L,(Fintype.card (Z i):ℝ)≤Knbr*(Aset i).card:=fun i hi=>(hSizes i hi).2.1
  have hWJ:∀i≤L,(Fintype.card (W i):ℝ)≤Knbr*(Bset i).card:=fun i hi=>(hSizes i hi).2.2
  have hPdomain:∀i≤L,∀x:W i,(1/2+γRich)*(Aset i).card≤(((P.comap (fV i)).neighborFinset x∩Aset i).card:ℝ):=fun i hi=>(hDegrees i hi).2.1
  have hPbal:∀i≤L,∀x:W i,|(((P.comap (fV i)).neighborFinset x∩Aset i).card:ℝ)-Dbal i|≤βQ*Scale i:=by
    intro i hi x
    simpa only [Scale,Dbal,hρeq] using (hDegrees i hi).1 x
  have hPreg:∀i≤L,∀x:W i,|((P.comap (fV i)).degree x:ℝ)-Dlevel i|≤βQ*Fintype.card (W i):=by
    intro i hi x
    simpa only [Dlevel,hρeq] using (hDegrees i hi).2.2.1 x
  have hPmin:∀i≤L,∀x:W i,(1/2+γRich)*Fintype.card (W i)≤((P.comap (fV i)).degree x:ℝ):=fun i hi=>(hDegrees i hi).2.2.2.1
  have hDL:∀i≤L,(Fintype.card (W i):ℝ)/2≤Dload i:=by
    intro i hi
    simpa only [Dload,Dlevel,hρeq] using (hDegrees i hi).2.2.2.2.1
  have hDU:∀i≤L,Dload i≤2*Fintype.card (W i):=by
    intro i hi
    simpa only [Dload,Dlevel,hρeq] using (hDegrees i hi).2.2.2.2.2
  have hwlevel:∀i≤L,SuccessorSequenceWeightConditions (P.comap (fV i)) (ρi i) (3*d) (Dload i) τLevel Aload Bload' (levelWeight i):=by
    simpa only [Dload,Dlevel,Aload,Bload',hρeq] using hWeight
  refine ⟨levelWeight,hwlevel,?_⟩
  exact hAll n hn U F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort vertices εHost he hdeg hbudgetV hbudgetE hτnonneg hτbound
    W Z Hdom hεHostAbs hmind fV gV ρi hGeometry.1 L hLsize hWsize hZsize hWstep hZlo hZhi hZW hZhi
    Aset Bset Scale hIsize hJsize hScale hAS hBS hInv hWS hZS hIstep hJstep hWI hZI hWJ (by
      intro i hi x
      convert hPdomain i hi x using 1 <;> congr 5 <;> exact Subsingleton.elim _ _)
    βQ hβQ hβQbal (by
      intro i hi x
      have hx:=hPbal i hi x
      have hdec:(Subtype.instDecidableEq : DecidableEq (W i))=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
      rw [hdec] at hx
      exact hx) Dlevel βQ hβQ hβQref hPreg hPmin bdom τLevel Aload levelWeight hDL hDU hwlevel hpstar0 hkstar0 htstar0
end Oberwolfach
