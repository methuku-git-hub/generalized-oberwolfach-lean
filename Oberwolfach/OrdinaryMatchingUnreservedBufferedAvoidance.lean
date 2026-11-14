module

public import Oberwolfach.OrdinaryMatchedSourceLiftMatchingInputs
public import Oberwolfach.OrdinaryMatchingUnreservedSourceAvoidance
public import Oberwolfach.OrdinaryPhysicalAssignedPayloadLength

@[expose] public section
/-! Lift the actual matched source pieces off the reserved components and
embed their buffered old pieces into the same physical matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U A B:Type} [Fintype U] [DecidableEq U] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem ordinary_matching_unreserved_buffered_with_avoidance
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (hm:2≤m)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (u:U)
    (index:A⊕B ≃ retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t Jret u)
    (hindex:∀b:B,∃a:{a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) a true},index (.inr b)=Sum.inr a):
    let Host:=ordinaryEligibleHost P π d
    let Rim:=ordinaryShiftedPairRims Host π d raw
    let H:=rawMarkedPairSpokes π d raw true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y))
    (i₀:Fin K) (Cres:Finset (F u).ConnectedComponent)
    (hCres:∀Q,Q∈Cres→Fintype.card Q=i₀.val+1)
    (assign:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u↪↥(Finset.univ\Cres))
    (hsize:∀a,Fintype.card (assign a).val=(a.val.val.1.getD i₀).val+1)
    (E:∀Q:(F u).ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card Q) ≃g Q.toSimpleGraph)
    (block:A⊕B↪LongReservedBlockIndex (F u) (Function.Embedding.subtype (fun Q:(F u).ConnectedComponent=>K<Fintype.card Q)) (m+1) d)
    (ext:∀i:A⊕B,Fin ((m+1)*d+5)↪Fin n)
    (hext:∀i,ext i=longReservedSigmaBlock (F u) (Function.Embedding.subtype (fun Q:(F u).ConnectedComponent=>K<Fintype.card Q)) (m+1) d
      (fun j=>E j.val) (block i) d le_rfl)
    (Paths:∀i,(F u).Walk (ext i 0) (ext i (Fin.last ((m+1)*d+4))))
    (hp:∀i,(Paths i).IsPath) (hlen:∀i,(Paths i).length=(m+1)*d+4)
    (hsupp:∀i,(Paths i).support=List.ofFn (ext i))
    (hP:∀i j,i≠j→Disjoint (Paths i).support.toFinset (Paths j).support.toFinset)
    (inner:∀a:A,Fin ((m+1)*d+1)↪Fin n) (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (root:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u→Fin n)
    (C:∀j,(F u).Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hverts:∀j,(C j).toSubgraph.verts=(assign j).val.supp)
    (hClen:∀j,(C j).length=Fintype.card (assign j).val)
    (hC:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (Paths i).support.toFinset (C j).support.toFinset),
    let S:Set (Fin n):={x | (F u).connectedComponentMk x∉Cres}
    let G:SimpleGraph S:=(F u).induce S
    let ER:={e:Fin n×Fin n // Rim (Sum.inl e)}
    let ES:={e:Fin n×Fin n // Rim (Sum.inr e)}
    let targetRoot:=fun i=>retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret u (index i);
    ∃ext':∀i:A⊕B,Fin ((m+1)*d+5)↪S,
    ∃Paths':∀i,G.Walk (ext' i 0) (ext' i (Fin.last ((m+1)*d+4))),
    ∃root':OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u→S,
    ∃C':∀j,G.Walk (root' j) (root' j),
    ∃inner':∀a:A,Fin ((m+1)*d+1)↪S,
    ∃(hp':∀i,(Paths' i).IsPath)
      (hP':∀i j,i≠j→Disjoint (Paths' i).support.toFinset (Paths' j).support.toFinset)
      (hlen':∀i,(Paths' i).length=(m+1)*d+4)
      (hcycle':∀j,(C' j).IsCycle)
      (hC':∀i j,i≠j→Disjoint (C' i).support.toFinset (C' j).support.toFinset)
      (hcross':∀i j,Disjoint (Paths' i).support.toFinset (C' j).support.toFinset),
      (∀i,(Paths' i).support=List.ofFn (ext' i)) ∧
      (∀i k,(ext' i k).val=ext i k) ∧ (∀a k,(inner' a k).val=inner a k) ∧
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
    let data:=actualResidualDataFromPacking G (fun i=>ext' i 0) (fun i=>ext' i (Fin.last ((m+1)*d+4))) Paths' hp' hP' (m+1) d (by omega) hd hlen'
      (fun e:ER=>e.val.1) (fun e:ER=>e.val.2) (fun e:ES=>e.val.1) (fun e:ES=>e.val.2) m (3*d) π (H false) (H true) M u targetRoot root' C' hcycle' hC' hcross';
    ∃ψ:S→Fin n,
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner'):Set S) ∧
      (∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext' i) j∈data.prescribed→
        ψ (bufferedMarker (m+1) d (ext' i) j)=(π^j.val) (targetRoot i)) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
        ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) (targetRoot r.1.val)) ∧
      (∀i∈data.s₂,∀j:Fin (d+1),∃x∈data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner',
        ψ x=(π^j.val) (targetRoot i)) ∧
      ActualOldImageDirected data ψ (rawMixedPhysicalArc Host π d raw) ∧ ActualOldPhysicalCoverage data ψ Pack ∧
      (∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>(m+1)*d) inner'→
        ψ x∉markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret u=>d) Subtype.val) ∧
      Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner').image ψ)
        (rawIntervalProtectedUnassignedList π d (fun e=>raw (Sum.inr e)) false true t Jret u) :=by
  intro Host Rim H RM state RR φ L hL i₀ Cres hCres assign hsize E block ext hext Paths hp hlen hsupp hP inner hinner root C hcycle hverts hClen hC hcross S G ER ES targetRoot
  have hlift:=ordinary_matched_source_lift_matching_inputs (F u) (hF u) Cres i₀ hCres assign (m+1) d E block ext hext Paths hp hlen hsupp inner hinner root C hcycle hverts hP hC hcross
  obtain ⟨hreg,ext',Paths',hPaths,hExt,root',C',hCycles,hRoot,hPathsDis,hCyclesDis,hCrossDis,inner',hInner,hInnerVal,hSrc⟩:=hlift
  have hp':∀i,(Paths' i).IsPath:=fun i=>(hPaths i).1
  have hlen':∀i,(Paths' i).length=(m+1)*d+4:=fun i=>(hPaths i).2.1
  have hsupp':∀i,(Paths' i).support=List.ofFn (ext' i):=fun i=>(hPaths i).2.2
  have hcycle':∀j,(C' j).IsCycle:=fun j=>(hCycles j).1
  have hlenPayload:=ordinary_physical_assigned_payload_length F hF π d m RM state L u i₀ Cres assign hsize
  have hClen':∀j,(C' j).length=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2:=
    fun j=>(hCycles j).2.1.trans ((hClen j).trans (hlenPayload j))
  have hfirst:=ordinary_matching_buffered_unreserved_source_with_avoidance (K:=K) (X:=S) hn G hreg P π d m hd hm hnoshort raw t Jret u index hindex
  have hsecond:=hfirst L hL
  have hresult:=hsecond (fun i=>ext' i 0) (fun i=>ext' i (Fin.last ((m+1)*d+4))) Paths' hp' hPathsDis hlen' ext' hsupp' hSrc inner' hInner root' C' hcycle' hCyclesDis hCrossDis hClen'
  exact ⟨ext',Paths',root',C',inner',hp',hPathsDis,hlen',hcycle',hCyclesDis,hCrossDis,hsupp',hExt,hInnerVal,hInner,hSrc,(fun j=>(hCycles j).2.2),hClen',hresult⟩
end Oberwolfach
