module

public import Oberwolfach.CandidateOrdinaryCoreUnreservedBufferedAllRimsDirectReserve
public import Oberwolfach.OrdinaryMatchedResidualPackageFromPacking
public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryCoreUnreservedBufferedAllRims
public import Oberwolfach.OrdinaryCoreUnreservedBufferedReserved
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedEligibleFiberNormalizationDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedMassAfterBoundedDeletionDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedMatchingAfterDeletionSupportDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedRetainedEventRootTargetsNativeDirectReserve
public import Oberwolfach.CandidateOrdinaryCoreEventMatchingSourceWalksAfterDeletionDirectReserve
public import Oberwolfach.CandidateOrdinaryCoreMatchingWalksWithTestsSupportDirectReserve
public import Oberwolfach.OrdinaryCoreMatchingWalksWithTestsSupport
public import Oberwolfach.OrdinaryAssignedMatchingRetainedMassBounds
public import Oberwolfach.OrdinaryMatchingUnreservedBufferedAllRims
public import Oberwolfach.OrdinarySourcePiecesAvoidReserved
public import Oberwolfach.OrdinaryCoreEventMatchingSourceWalksAfterDeletion
public import Oberwolfach.OrdinaryMatchingBufferedSourceOccupancy
public import Oberwolfach.OrdinaryShiftedMatchingCoreEvent
public import Oberwolfach.OrdinaryCapacityAutomaticMargins
public import Oberwolfach.OrdinaryReservedPathsShortCyclesOriented
public import Oberwolfach.OrdinaryAssignedRetainedEventRootTargetsNative
public import Oberwolfach.MixedOutcomeAnchorEmbedding
public import Oberwolfach.OrdinaryAllHubReservedPaths
public import Oberwolfach.OrdinaryAssignedMatchingAfterDeletionSupport
public import Oberwolfach.OrdinaryMixedGenericPhysicalMatchingSupport
public import Oberwolfach.OrdinaryAssignedMassAfterBoundedDeletion
public import Oberwolfach.OrdinaryAssignedEligibleFiberNormalization
public import Oberwolfach.OrdinaryPhysicalMatchingCardinality

@[expose] public section
/-! For every bounded physical rim deletion, match the actual retained
ordinary factor-frequency tests on the same sample and control every physical
rim and spoke row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_matching_supplies_residual_packages_direct_reserve
    (r K m d:ℕ) (hr:2≤r) (hK3:3≤K) (hm:7≤m) (hd:2≤d)
    (hrM:2*(m+1)≤r) (hrO:∀i:Fin K,2*(longPaddedSeedExponent i+2)≤r)
    (θ α γ Kcd BM:ℝ) (hθ:0<θ) (hθ1:θ≤1/100) (hα:0<α) (hγ:0<γ) (hKcd:0<Kcd) (hBM:0≤BM)
    (hαbound:α≤θ/(1600*(K:ℝ)*(K:ℝ)))
    (BO:Fin K→ℝ) (hBO:∀i,0≤BO i)
    (hKpair:(∑i:Option (Fin K),(16:ℝ)*(match i with
      | none=>((m:ℝ)+1)^4*BM
      | some i=>((longPaddedSeedExponent i:ℝ)+2)^3*BO i))≤Kcd)
    (hcutHost:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2):
    ∃ε:ℝ,0<ε ∧ ∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (i₀:Fin K) (rsv ρ D:ℝ) (hs0:0≤rsv) (hs1:rsv≤1/100)
      (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
      (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
      (pstar:ℝ) (hpstar:0<pstar)
      (P_1 Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (δ:ℝ) (hDel:∀x,(Del.degree x:ℝ)≤δ)
      (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
      (hwM:∀W,0≤wM W ∧ wM W≤BM/(n:ℝ)^m)
      (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
      (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(longPaddedSeedExponent i+1))
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
      (τ t countErr:ℝ) (ht:0≤t) (hτ:τ≤1/2) (hcountErr:countErr≤pstar*n/2)
      (lam:ℝ) (hlam:0≤lam) (hτ0:0≤τ) (hcount0:0≤countErr)
      (hτrate:τ≤lam*pstar/4) (hcountRate:countErr≤lam*pstar*n/4)
      (hslack:lam+γ*(1-θ+lam)<θ)
      (weights:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P_1 π d) (longPaddedSeedExponent i+2)→ℝ)
      (hNamed:wO=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ ((m:ℝ)+1) D (ordinaryEligibleHost P_1 π d) π d weights)
      (Cres:∀u,Finset (F u).ConnectedComponent)
      (hCres:∀u c,c∈Cres u→Fintype.card c=i₀.val+1)
      (hres:∀u,((i₀.val+1:ℕ):ℝ)*((Cres u).card:ℝ)=rsv*n),
    let c:ℝ:=(m:ℝ)+1
    let a:=ordinaryAssignedLongWeight F hF K θ c
    let b:=ordinaryAssignedShortWeight F hF K i₀ rsv θ c
    let p:=(∑u,(a u+b u))/D
    let η:=fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw Del.edgeFinset
    let old:=typedMarkedResourceState (ordinaryShiftedPairRims (ordinaryEligibleHost P_1 π d) π d raw) (rawMarkedPairSpokes π d raw true true)
    let state:=typedMarkedResourceState (ordinaryShiftedPairRims (ordinaryEligibleHost P_1 π d) π d raw') (rawMarkedPairSpokes π d raw' true true)
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let w:=ordinaryMixedGenericWeight wM wO
    let target:=ordinaryMixedIdealTarget (V:=Fin n) (m:ℝ) D p a b η
    let loss:Option (Fin K)→ℝ:=fun i=>match i with
      | none=>22*((m:ℝ)+1)^4*BM
      | some i=>10*((longPaddedSeedExponent i:ℝ)+2)^4*BO i
    let terr:=t+(∑i,loss i)*δ/(n:ℝ)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let W:=PhysicalSampledActive φ state
    let Cand:=PhysicalSampledCandidate (mixedCandidateResources R) state
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources R) state
    let rows:=fun j:OrdinaryPhysicalRowIndex (Fin n) U=>physicalSampledRow φ state (ordinaryPhysicalRow j)
    let tests:=OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ
    let g:=fun z:tests=>fun c:Cand=>ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z c.val;
    (∀u,pstar≤b u)→(terr≤θ/(800*(K:ℝ)))→(terr≤lam*(θ/(100*(K:ℝ)))/4)→
    (4*((K:ℝ)+1)*terr+τ≤ε)→
    ∀(εHost A BMbase k₂:ℝ) (hk₂:0≤k₂)
      (weight:(Fin (m+1)→Fin n)→ℝ)
      (hw:SuccessorSequenceWeightConditions (ordinaryEligibleHost P_1 π d) π (3*d) D τ A BMbase weight)
      (hNamedM:wM=ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight)
      (hw0:∀i C,0≤weights i C) (Bbase:Fin K→ℝ) (hBbase:∀i,0≤Bbase i)
      (hwbase:∀i C,weights i C≤Bbase i/(n:ℝ)^(longPaddedSeedExponent i))
      (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,(∑C,if C.val.val.Adj x y then weights i C else 0)=if (ordinaryEligibleHost P_1 π d).Adj x y then 1 else 0)
      (hdeg:∀x,|((ordinaryEligibleHost P_1 π d).degree x:ℝ)-D|≤εHost*(n:ℝ))
      (hbudgetS:∀i∈longRetainedSeedIndices F hF K θ,6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(Bbase i)*(2*(3*d))+εHost*(n:ℝ)≤τ*D)
      (hbudgetR:∀i∈longRetainedSeedIndices F hF K θ,5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(Bbase i)*(2*(3*d))/(n:ℝ)≤τ)
      (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c;
    (∀u g,0≤q u g)→(∀u,∑g,q u g≤1/8)→
    (∀u j,0≤s u j)→(∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))→
    (2*p+2*k₂≤1)→
    ∀ξ:ℝ,ξ*(n:ℝ)≤countErr→
    OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P_1 π d) π d m p k₂ q s wM wO t ξ σ→
    ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) tret),
    ∃L:Finset Cand,
      let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
      let AM:=fun u=>OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u
      let AU:=fun u=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
      let payload:=fun u=>ordinaryPhysicalUnmarkedPayload π d m RM state L u
      let plen:=fun u (a:AU u)=>longPaddedSeedExponent (payload u a).1+2
      let Host:=ordinaryEligibleHost P_1 π d
      let Rim:=ordinaryShiftedPairRims Host π d raw'
      let H:=rawMarkedPairSpokes π d raw' true true
      let ER:={e:Fin n×Fin n // Rim (Sum.inl e)}
      let ES:={e:Fin n×Fin n // Rim (Sum.inr e)}
      let MW:=MarkedWheel (fun e:ER=>e.val.1) (fun e:ER=>e.val.2) (fun e:ES=>e.val.1) (fun e:ES=>e.val.2) m π (3*d) (H false) (H true)
      let W:=fun u=>AM u→MW
      let Good:=fun u (w:W u)=>∀a,(w a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (w a).2.val=u
      let Pack:=fun u (w:W u)=>mixedWheelRimPack (plen u) (Finset.univ.image w) (fun a=>(payload u a).2)
      let Final:=fun u=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false tret Jret u
      let Approx:=fun u=>{a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) a true}
      let root:=fun u=>retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true tret Jret u
      let S:=fun u:U=>{x:Fin n | (F u).connectedComponentMk x∉Cres u}
      let G:=fun u=>(F u).induce (S u)
      let Pos:=fun u (w:W u) (i:Approx u)=>packedPhysicalSpokePositions
        (fun e:ER=>e.val.1) (fun e:ER=>e.val.2) (fun e:ES=>e.val.1) (fun e:ES=>e.val.2)
        m (3*d) d π (H false) (H true) (Finset.univ.image w) u (root u (.inr i))
      let Arc:=rawMixedPhysicalArc Host π d raw'
      let Avail:=fun u=>rawIntervalProtectedUnassignedList π d (fun e=>raw (Sum.inr e)) false true tret Jret u
      let Reserve:=fun u=>rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) u;
      (∀x∈L,∀y∈L,x≠y→Disjoint (Q x) (Q y)) ∧
      (∀j,(((rows j)\L.biUnion Q).card:ℝ)≤(max α γ)*n) ∧
      (∀u,(1-θ-(lam+γ*(1-θ+lam)))*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤
        ((∑a:AU u,plen u a):ℝ) ∧
        ((∑a:AU u,plen u a):ℝ)≤
        (1-θ+(lam+γ*(1-θ+lam)))*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)) ∧
      ∀u,Nonempty (OrdinaryMatchedResidualHubPackage (G u) m d π (root u) Arc (Avail u) (Reserve u)
        (Good u) (Pack u) (Pos u) (plen u)) :=by
  obtain ⟨ε,hε,N,hN⟩:=ordinary_core_unreserved_buffered_matching_with_all_packed_rims_candidate_direct_reserve
    r K m d hr hK3 hm hd hrM hrO θ α γ Kcd BM hθ hθ1 hα hγ hKcd hBM hαbound BO hBO hKpair hcutHost
  refine ⟨ε,hε,N,?_⟩
  intro n hn hn0 U _ _ hU F hF Allowed hAllowed i₀ rsv ρ D hs0 hs1 hda hρ hρ1 hD hsize hClassReserve pstar hpstar P_1 Del π δ hDel wM hwM wO hwO σ τ t countErr ht hτ hcountErr lam hlam hτ0 hcount0 hτrate hcountRate hslack weights hNamed Cres hCres hres
    c a b p η raw raw' old state R w target loss terr φ Wraw Cand Q rows tests g hbstar hterr hrelative herr
    εHost Aconst BMbase k₂ hk₂ weight hw hNamedM hw0 Bbase hBbase hwbase he hdeg hbudgetS hbudgetR hnoshort q s hq hQ hs hS hsum ξ hξ hcore tret Jret
  obtain ⟨L,hdev,hsupp,hL,hrows,hlo,hhi,hmass,hall⟩:=hN n hn hn0 U hU F hF Allowed hAllowed i₀ rsv ρ D hs0 hs1 hda hρ hρ1 hD hsize hClassReserve pstar hpstar P_1 Del π δ hDel wM hwM wO hwO σ τ t countErr ht hτ hcountErr lam hlam hτ0 hcount0 hτrate hcountRate hslack weights hNamed Cres hCres hres
    hbstar hterr hrelative herr εHost Aconst BMbase k₂ hk₂ weight hw hNamedM hw0 Bbase hBbase hwbase he hdeg hbudgetS hbudgetR hnoshort hq hQ hs hS hsum ξ hξ hcore tret Jret
  refine ⟨L,hL,?_,?_,?_⟩
  · intro j
    simpa only [mul_comm] using hrows j
  · intro u
    simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_ofNat] using hmass u
  · intro u
    obtain ⟨f,hf,g',hg,hgraph,ψold,hψold,E,block,ext,inner,hext,hinner,hextdis,Paths,root',C,hp,hlen,hsupp,hP,hcycle,hClen,horient,hsupport,hC,hcross,anchor,hanchor,hresidual⟩:=hall u
    obtain ⟨ext',Paths',root'',C',inner',hp',hP',hlen',hcycle',hC',hcross',hsupp',hext',hinner',hinnerEq',hextdis',hCmap,hClen',W,hW,ψ,hψ,hmarker,hruns,hcontains,hdir,hcoverage,hrootavoid,havoid,hreserve,hrims⟩:=hresidual
    exact ordinary_matched_residual_package_from_packing _ m d (by omega) (by omega) π _ ext' inner' Paths' hp' hP' hlen' hsupp' hinnerEq'
      root'' C' hcycle' hC' hcross' _ hClen' _ _ _ _ (3*d) _ _ u
      (fun w=>Finset.univ.image w) _ _ W hW ψ _ _ _ hmarker hψ havoid hreserve hdir hcoverage hrims
end Oberwolfach
