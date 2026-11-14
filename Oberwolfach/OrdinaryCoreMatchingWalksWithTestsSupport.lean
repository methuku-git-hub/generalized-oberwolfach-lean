module

public import Oberwolfach.OrdinaryCommonEventMatchingWalksWithTestsSupport
public import Oberwolfach.OrdinaryCommonEventMatchingSourceWalksAfterDeletion
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

theorem ordinary_core_event_matching_source_walks_with_tests_support
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
      (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
      (pstar:ℝ) (hpstar:0<pstar)
      (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (δ:ℝ) (hDel:∀x,(Del.degree x:ℝ)≤δ)
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
      (weights:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
      (hNamed:wO=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ ((m:ℝ)+1) D (ordinaryEligibleHost P π d) π d weights)
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
    let old:=typedMarkedResourceState (ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw) (rawMarkedPairSpokes π d raw true true)
    let state:=typedMarkedResourceState (ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw') (rawMarkedPairSpokes π d raw' true true)
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
      (hw:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A BMbase weight)
      (hNamedM:wM=ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight)
      (hw0:∀i C,0≤weights i C) (Bbase:Fin K→ℝ) (hBbase:∀i,0≤Bbase i)
      (hwbase:∀i C,weights i C≤Bbase i/(n:ℝ)^(longPaddedSeedExponent i))
      (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,(∑C,if C.val.val.Adj x y then weights i C else 0)=if (ordinaryEligibleHost P π d).Adj x y then 1 else 0)
      (hdeg:∀x,|((ordinaryEligibleHost P π d).degree x:ℝ)-D|≤εHost*(n:ℝ))
      (hbudgetS:∀i∈longRetainedSeedIndices F hF K θ,6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(Bbase i)*(2*(3*d))+εHost*(n:ℝ)≤τ*D)
      (hbudgetR:∀i∈longRetainedSeedIndices F hF K θ,5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(Bbase i)*(2*(3*d))/(n:ℝ)≤τ)
      (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c;
    (∀u g,0≤q u g)→(∀u,∑g,q u g≤1/8)→
    (∀u j,0≤s u j)→(∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))→
    (2*p+2*k₂≤1)→
    ∀ξ:ℝ,ξ*(n:ℝ)≤countErr→
    OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p k₂ q s wM wO t ξ σ→
    ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) tret),
    ∃L:Finset Cand,
      let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
      let A:=fun u=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
      let payload:=fun u=>ordinaryPhysicalUnmarkedPayload π d m RM state L u;
      (∀z:tests,|((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*(∑x:Cand,g z x*mixedCandidateWeight w x.val)-
        (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n|≤
        lam*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n) ∧
      (∀x∈L,0<mixedCandidateWeight w x.val) ∧
      (∀x∈L,∀y∈L,x≠y→Disjoint (Q x) (Q y)) ∧
      (∀j,(((rows j)\L.biUnion Q).card:ℝ)≤max α γ*n) ∧
      (∀z,(1-γ)*(∑x:Cand,g z x*mixedCandidateWeight w x.val)≤∑x∈L,g z x) ∧
      (∀z,(∑x∈L,g z x)≤(1+γ)*(∑x:Cand,g z x*mixedCandidateWeight w x.val)) ∧
      ∀u,∃f:A u↪↥(Finset.univ\Cres u),
        (∀a,Fintype.card (f a).val=(a.val.val.1.getD i₀).val+1) ∧
        ∃g:∀a,(f a).val↪Fin n,
          (∀a,Set.range (g a)=Set.range (payload u a).2.1.val) ∧
          (∀a (x y:(f a).val),(f a).val.toSimpleGraph.Adj x y↔
            (ordinaryWheelRim (orderedOrdinaryUniversalWheel (by have h:=long_padded_seed_exponent_positive (payload u a).1;omega) (payload u a).2)).Adj (g a x) (g a y)) ∧
        ∃ψ:{v:Fin n // ∃a,v∈((f a).val).supp}↪Fin n,
          (∀a (x:(f a).val),ψ ⟨x.val,⟨a,x.property⟩⟩=g a x) ∧
        let T:=retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true tret Jret u
        let I:={C:(F u).ConnectedComponent // K<Fintype.card C}
        let longs:I↪(F u).ConnectedComponent:=Function.Embedding.subtype _;
        let cycles:A u↪(F u).ConnectedComponent:=f.trans (Function.Embedding.subtype _);
        ∃E:∀C:(F u).ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
        ∃block:T↪LongReservedBlockIndex (F u) longs (m+1) d,
        ∃ext:∀a:T,Fin ((m+1)*d+5)↪Fin n,
        ∃inner:∀a:T,Fin ((m+1)*d+1)↪Fin n,
          (∀i,ext i=longReservedSigmaBlock (F u) longs (m+1) d (fun j=>E (longs j)) (block i) d (le_rfl)) ∧
          (∀a j,inner a j=ext a ⟨j.val+2,by omega⟩) ∧
          (∀a b,a≠b→Disjoint (Finset.univ.image (ext a)) (Finset.univ.image (ext b))) ∧
        ∃(P:∀i:T,(F u).Walk (ext i 0) (ext i (Fin.last ((m+1)*d+4))))
          (root:A u→Fin n) (C:∀j:A u,(F u).Walk (root j) (root j)),
          (∀i,(P i).IsPath) ∧ (∀i,(P i).length=(m+1)*d+4) ∧ (∀i,(P i).support=List.ofFn (ext i)) ∧
          (∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset) ∧
          (∀j,(C j).IsCycle) ∧ (∀j,(C j).length=Fintype.card (cycles j)) ∧
          (∀j k,k<(C j).length→factorCycleOrientation (F u) E ((C j).getVert k)=(C j).getVert (k+1)) ∧
          (∀j,(C j).toSubgraph.verts=(cycles j).supp) ∧
          (∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset) ∧
          (∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset) ∧
        let Marks:=Finset.univ.image (fun z:T×Fin (d+1)=>bufferedMarker (m+1) d (ext z.1) z.2);
        ∃anchor:{x // x∈Marks}↪Fin n,
          ∀i (j:Fin (d+1)),anchor ⟨bufferedMarker (m+1) d (ext i) j,
            Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩⟩=
            (π^j.val) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true tret Jret u i) :=by
  obtain ⟨ε,hε,N,hmatch⟩:=ordinary_common_event_matching_source_walks_with_tests_support
    r K m d hr hK3 hm hd hrM hrO θ α γ Kcd BM hθ hθ1 hα hγ hKcd hBM hαbound BO hBO hKpair hcutHost
  refine ⟨ε,hε,N,?_⟩
  intro n hn hn0 U _ _ hU F hF Allowed hAllowed i₀ rsv ρ D hs0 hs1 hda hρ hρ1 hD hsize hsclass hclass pstar hpstar P Del π δ hDel wM hwM wO hwO σ τ t countErr ht hτ hcountErr lam hlam hτ0 hcount0 hτrate hcountRate hslack weights hNamed Cres hCres hres
    c a b p η raw raw' old state R w target loss terr φ W Cand Q rows tests g hbstar hterr hrelative herr
    εHost A BMbase k₂ hk₂ weight hw hNamedM hw0 Bbase hBbase hwbase he hdeg hbudgetS hbudgetR hnoshort q s hq hQ hs hS hsum ξ hξ hcore tret Jret
  exact hmatch n hn hn0 U hU F hF Allowed hAllowed i₀ rsv ρ D hs0 hs1 hda hρ hρ1 hD hsize hsclass hclass pstar hpstar P Del π δ hDel wM hwM wO hwO σ τ t countErr ht hτ hcountErr lam hlam hτ0 hcount0 hτrate hcountRate hslack weights hNamed Cres hCres hres
    hbstar hterr hrelative herr εHost A BMbase k₂ hk₂ weight hw hNamedM hw0 Bbase hBbase hwbase he hdeg hbudgetS hbudgetR hnoshort hq hQ hs hS hsum ξ hξ hcore tret Jret
end Oberwolfach
