module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryCoreUnreservedBufferedAllRims
public import Oberwolfach.OrdinaryCoreUnreservedBufferedReserved
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedEligibleFiberNormalizationDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedMassAfterBoundedDeletionDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedMatchingAfterDeletionSupportDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedRetainedEventRootTargetsNativeDirectReserve
public import Oberwolfach.CandidateOrdinaryCoreEventMatchingSourceWalksAfterDeletionDirectReserve
public import Oberwolfach.OrdinaryCandidateCoreWalksLocalRows
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

theorem ordinary_candidate_core_packages_local_rows
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
      (P_1 Del:SimpleGraph (Fin n)) (Inner:Finset (Fin n)) (π:Equiv.Perm (Fin n)) (δ:ℝ) (hDel:∀x,(Del.degree x:ℝ)≤δ)
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
    let ι:W↪Sym2 (Fin n)⊕(Fin n×U):=Function.Embedding.subtype _
    let localRows:=fun v:Fin n=>ordinaryLocalRimIncidence ι v Inner
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
      let A:=fun u=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
      let payload:=fun u=>ordinaryPhysicalUnmarkedPayload π d m RM state L u;
      (∀z:tests,|((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*(∑x:Cand,g z x*mixedCandidateWeight w x.val)-
        (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n|≤
        lam*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n) ∧
      (∀x∈L,0<mixedCandidateWeight w x.val) ∧
      (∀x∈L,∀y∈L,x≠y→Disjoint (Q x) (Q y)) ∧
      (∀j,(((rows j)\L.biUnion Q).card:ℝ)≤max α γ*n) ∧
      (∀v,(((localRows v)\L.biUnion Q).card:ℝ)≤max (α*n) (γ*Inner.card)) ∧
      (∀z,(1-γ)*(∑x:Cand,g z x*mixedCandidateWeight w x.val)≤∑x∈L,g z x) ∧
      (∀z,(∑x∈L,g z x)≤(1+γ)*(∑x:Cand,g z x*mixedCandidateWeight w x.val)) ∧
      (∀u,(1-θ-(lam+γ*(1-θ+lam)))*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤
        ((∑a:A u,(longPaddedSeedExponent (payload u a).1+2)):ℝ) ∧
        ((∑a:A u,(longPaddedSeedExponent (payload u a).1+2)):ℝ)≤
        (1-θ+(lam+γ*(1-θ+lam)))*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)) ∧
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
          ∃(hp:∀i,(P i).IsPath) (hlen:∀i,(P i).length=(m+1)*d+4)
            (hsupp:∀i,(P i).support=List.ofFn (ext i))
            (hP:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
            (hcycle:∀j,(C j).IsCycle) (hClen:∀j,(C j).length=Fintype.card (cycles j)),
          (∀j k,k<(C j).length→factorCycleOrientation (F u) E ((C j).getVert k)=(C j).getVert (k+1)) ∧
          (∀j,(C j).toSubgraph.verts=(cycles j).supp) ∧
          ∃(hC:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
            (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset),
        let Marks:=Finset.univ.image (fun z:T×Fin (d+1)=>bufferedMarker (m+1) d (ext z.1) z.2);
        ∃anchor:{x // x∈Marks}↪Fin n,
          (∀i (j:Fin (d+1)),anchor ⟨bufferedMarker (m+1) d (ext i) j,
            Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩⟩=
            (π^j.val) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true tret Jret u i)) ∧
        let Final:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false tret Jret u
        let Approx:={a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) a true}
        let index:Final⊕Approx ≃ T:=Equiv.refl T
        let ext₁:=fun i:Final⊕Approx=>ext (index i)
        let Host:=ordinaryEligibleHost P_1 π d
        let Rim:=ordinaryShiftedPairRims Host π d raw'
        let H:=rawMarkedPairSpokes π d raw' true true
    let S:Set (Fin n):={x | (F u).connectedComponentMk x∉Cres u}
    let G:SimpleGraph S:=(F u).induce S
    let ER:={e:Fin n×Fin n // Rim (Sum.inl e)}
    let ES:={e:Fin n×Fin n // Rim (Sum.inr e)}
    let targetRoot:=fun i=>retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true tret Jret u (index i);
    ∃ext':∀i:Final⊕Approx,Fin ((m+1)*d+5)↪S,
    ∃Paths':∀i,G.Walk (ext' i 0) (ext' i (Fin.last ((m+1)*d+4))),
    ∃root':OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u→S,
    ∃C':∀j,G.Walk (root' j) (root' j),
    ∃inner':∀a:Final,Fin ((m+1)*d+1)↪S,
    ∃(hp':∀i,(Paths' i).IsPath)
      (hP':∀i j,i≠j→Disjoint (Paths' i).support.toFinset (Paths' j).support.toFinset)
      (hlen':∀i,(Paths' i).length=(m+1)*d+4)
      (hcycle':∀j,(C' j).IsCycle)
      (hC':∀i j,i≠j→Disjoint (C' i).support.toFinset (C' j).support.toFinset)
      (hcross':∀i j,Disjoint (Paths' i).support.toFinset (C' j).support.toFinset),
      (∀i,(Paths' i).support=List.ofFn (ext' i)) ∧
      (∀i k,(ext' i k).val=ext₁ i k) ∧ (∀a k,(inner' a k).val=inner (.inl a) k) ∧
      (∀a k,inner' a k=ext' (.inl a) ⟨k.val+2,by omega⟩) ∧
      (∀i j,i≠j→Disjoint (Finset.univ.image (ext' i)) (Finset.univ.image (ext' j))) ∧
      (∀j,(C' j).support.map Subtype.val=(C j).support) ∧
      (∀j,(C' j).length=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2) ∧
    ∃W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:ER=>e.val.1) (fun e:ER=>e.val.2)
        (fun e:ES=>e.val.1) (fun e:ES=>e.val.2) m π (3*d) (H false) (H true),
      (∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u) ∧
    let M:=Finset.univ.image W
    let Pack:=mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)
      M (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2)
    let data:=actualResidualDataFromPacking G (fun i=>ext' i 0) (fun i=>ext' i (Fin.last ((m+1)*d+4))) Paths' hp' hP' (m+1) d (by omega) (by omega) hlen'
      (fun e:ER=>e.val.1) (fun e:ER=>e.val.2) (fun e:ES=>e.val.1) (fun e:ES=>e.val.2) m (3*d) π (H false) (H true) M u targetRoot root' C' hcycle' hC' hcross';
    ∃ψ:S→Fin n,
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner'):Set S) ∧
      (∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext' i) j∈data.prescribed→
        ψ (bufferedMarker (m+1) d (ext' i) j)=(π^j.val) (targetRoot i)) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
        ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) (targetRoot r.1.val)) ∧
      (∀i∈data.s₂,∀j:Fin (d+1),∃x∈data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner',
        ψ x=(π^j.val) (targetRoot i)) ∧
      ActualOldImageDirected data ψ (rawMixedPhysicalArc Host π d raw') ∧ ActualOldPhysicalCoverage data ψ Pack ∧
      (∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>(m+1)*d) inner'→
        ψ x∉markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false tret Jret u=>d) Subtype.val) ∧
      Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner').image ψ)
        (rawIntervalProtectedUnassignedList π d (fun e=>raw (Sum.inr e)) false true tret Jret u) ∧
      Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner').image ψ)
        (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) u) ∧
      (∀edge∈Pack,∃(e:Sym2 (Fin n)),e∈data.deletedEdges.image (Sym2.map ψ) ∧ e.toFinset=edge) :=by
  obtain ⟨ε,hε,N,hmatch⟩:=ordinary_candidate_core_walks_local_rows
    r K m d hr hK3 hm hd hrM hrO θ α γ Kcd BM hθ hθ1 hα hγ hKcd hBM hαbound BO hBO hKpair hcutHost
  refine ⟨ε,hε,N,?_⟩
  intro n hn hn0 U _ _ hU F hF Allowed hAllowed i₀ rsv ρ D hs0 hs1 hda hρ hρ1 hD hsize hClassReserve pstar hpstar P_1 Del Inner π δ hDel wM hwM wO hwO σ τ t countErr ht hτ hcountErr lam hlam hτ0 hcount0 hτrate hcountRate hslack weights hNamed Cres hCres hres
    c a b p η raw raw' old state R w target loss terr φ W Cand Q rows ι localRows tests g hbstar hterr hrelative herr
    εHost Aconst BMbase k₂ hk₂ weight hw hNamedM hw0 Bbase hBbase hwbase he hdeg hbudgetS hbudgetR hnoshort q s hq hQ hs hS hsum ξ hξ hcore tret Jret
  obtain ⟨L,hdev,hsupp,hL,hrows,hlocal,hlo,hhi,hall⟩:=hmatch n hn hn0 U hU F hF Allowed hAllowed i₀ rsv ρ D hs0 hs1 hda hρ hρ1 hD hsize hClassReserve pstar hpstar P_1 Del Inner π δ hDel wM hwM wO hwO σ τ t countErr ht hτ hcountErr lam hlam hτ0 hcount0 hτrate hcountRate hslack weights hNamed Cres hCres hres
    hbstar hterr hrelative herr εHost Aconst BMbase k₂ hk₂ weight hw hNamedM hw0 Bbase hBbase hwbase he hdeg hbudgetS hbudgetR hnoshort hq hQ hs hS hsum ξ hξ hcore tret Jret
  refine ⟨L,hdev,hsupp,hL,hrows,hlocal,hlo,hhi,?_,?_⟩
  · let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    have hbound:=ordinary_assigned_matching_retained_mass_bounds F hF i₀ rsv θ π d m RM c D
      (ordinaryEligibleHost P_1 π d) weights wM state L lam γ hγ.le
    apply hbound
    · simpa only [w,hNamed] using hsupp
    · convert hdev using 1 <;> (try simp only [g,tests,w,hNamed]) <;> congr! 5
    · convert hlo using 1 <;> (try simp only [g,tests,w,hNamed]) <;> congr! 5
    · convert hhi using 1 <;> (try simp only [g,tests,w,hNamed]) <;> congr! 5
  · intro u
    obtain ⟨f,hf,g,hg,hgraph,ψ,hψ,E,block,ext,inner,hext,hinner,hextdis,Paths,root,C,hp,hlen,hsupp,hP,hcycle,hClen,horient,hsupport,hC,hcross,anchor,hanchor⟩:=hall u
    refine ⟨f,hf,g,hg,hgraph,ψ,hψ,E,block,ext,inner,hext,hinner,hextdis,Paths,root,C,hp,hlen,hsupp,hP,hcycle,hClen,horient,hsupport,hC,hcross,anchor,hanchor,?_⟩
    let T:=retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true tret Jret u
    let Final:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false tret Jret u
    let Approx:={a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) a true}
    let index:Final⊕Approx ≃ T:=Equiv.refl T
    let block₁:=index.toEmbedding.trans block
    let ext₁:=fun i:Final⊕Approx=>ext (index i)
    let Paths₁:=fun i:Final⊕Approx=>Paths (index i)
    let innerFinal:=fun a:Final=>inner (.inl a)
    have hext₁:∀i,ext₁ i=longReservedSigmaBlock (F u) (Function.Embedding.subtype (fun Q:(F u).ConnectedComponent=>K<Fintype.card Q)) (m+1) d
        (fun j=>E j.val) (block₁ i) d le_rfl:=fun i=>hext (index i)
    have hp₁:∀i,(Paths₁ i).IsPath:=fun i=>hp (index i)
    have hlen₁:∀i,(Paths₁ i).length=(m+1)*d+4:=fun i=>hlen (index i)
    have hsupp₁:∀i,(Paths₁ i).support=List.ofFn (ext₁ i):=fun i=>hsupp (index i)
    have hP₁:∀i j,i≠j→Disjoint (Paths₁ i).support.toFinset (Paths₁ j).support.toFinset:=
      fun i j hij=>hP (index i) (index j) (fun he=>hij (index.injective he))
    have hinner₁:∀a k,innerFinal a k=ext₁ (.inl a) ⟨k.val+2,by omega⟩:=fun a k=>hinner (.inl a) k
    have hcross₁:∀i j,Disjoint (Paths₁ i).support.toFinset (C j).support.toFinset:=fun i j=>hcross (index i) j
    have hClen₁:∀j,(C j).length=Fintype.card (f j).val:=fun j=>hClen j
    have hfirst:=ordinary_matching_unreserved_buffered_with_all_packed_rims (K:=K) (A:=Final) (B:=Approx) hn0 F hF P_1 π d m (by omega) (by omega) hnoshort raw' tret Jret u index (fun b=>⟨b,rfl⟩) (fun a=>⟨a,rfl⟩)
    have hsecond:=hfirst L hL
    exact hsecond i₀ (Cres u) (hCres u) f hf E block₁ ext₁ hext₁ Paths₁ hp₁ hlen₁ hsupp₁ hP₁ innerFinal hinner₁ root C hcycle hsupport hClen₁ hC hcross₁
end Oberwolfach
