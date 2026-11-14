module

public import Oberwolfach.OrdinaryPhysicalMatchingNamedWheelFamily
public import Oberwolfach.OrdinaryMixedSourceBufferedCoverage
public import Oberwolfach.MixedWheelRimPacksDisjoint
public import Oberwolfach.OrdinaryMixedSourceBufferedEmbedding
public import Oberwolfach.OrdinaryPhysicalAssignedPayloadLength
public import Oberwolfach.AssignedOrdinaryWheelReindex

@[expose] public section
/-! The physical matching's own wheels embed the matched short cycles and
selected runs of the reserved factor paths on that same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U A B:Type} [Fintype U] [DecidableEq U] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem ordinary_matching_buffered_source_embedding_with_coverage
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (hm:2≤m)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (u:U)
    (index:A⊕B ≃ retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t Jret u):
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
    (assign:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u↪↥(Finset.univ\Cres))
    (hsize:∀a,Fintype.card (assign a).val=(a.val.val.1.getD i₀).val+1)
    (u₀ v₀:A⊕B→Fin n) (Paths:∀i,(F u).Walk (u₀ i) (v₀ i))
    (hp:∀i,(Paths i).IsPath) (hP:∀i j,i≠j→Disjoint (Paths i).support.toFinset (Paths j).support.toFinset)
    (hlen:∀i,(Paths i).length=(m+1)*d+4) (ext:∀i:A⊕B,Fin ((m+1)*d+5)↪Fin n)
    (hsupp:∀i,(Paths i).support=List.ofFn (ext i))
    (hsrc:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (inner:∀a:A,Fin ((m+1)*d+1)↪Fin n) (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (root:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u→Fin n)
    (C:∀j,(F u).Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hC:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (Paths i).support.toFinset (C j).support.toFinset)
    (hClen:∀j,(C j).length=Fintype.card (assign j).val),
    let E:={e:Fin n×Fin n // Rim (Sum.inl e)}
    let S:={e:Fin n×Fin n // Rim (Sum.inr e)}
    let targetRoot:=fun i=>retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret u (index i);
    ∃W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:E=>e.val.1) (fun e:E=>e.val.2)
      (fun e:S=>e.val.1) (fun e:S=>e.val.2) m π (3*d) (H false) (H true),
    (∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u) ∧
    let M:=Finset.univ.image W
    let Pack:=mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)
      M (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2);
    let data:=actualResidualDataFromPacking (F u) u₀ v₀ Paths hp hP (m+1) d (by omega) hd hlen
      (fun e:E=>e.val.1) (fun e:E=>e.val.2) (fun e:S=>e.val.1) (fun e:S=>e.val.2) m (3*d) π (H false) (H true) M u targetRoot root C hcycle hC hcross;
    ∃ψ:Fin n→Fin n,
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner):Set (Fin n)) ∧
      (∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext i) j∈data.prescribed→
        ψ (bufferedMarker (m+1) d (ext i) j)=(π^j.val) (targetRoot i)) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
        ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) (targetRoot r.1.val)) ∧
      ActualOldImageDirected data ψ (rawMixedPhysicalArc Host π d raw) ∧ ActualOldPhysicalCoverage data ψ Pack :=by
  intro Host Rim H RM state RR φ L hL i₀ Cres assign hsize u₀ v₀ Paths hp hP hlen ext hsupp hsrc inner hinner root C hcycle hC hcross hClen E S targetRoot
  letI:Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  let T:=OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
  let len:=fun a:T=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2
  let Q:=fun a:T=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2
  have hfamily:=ordinary_physical_matching_named_wheel_family (K:=K) P π d m raw
  have hfamilyL:=hfamily L
  have hfamilyMatch:=hfamilyL hL
  obtain ⟨W,hW,hMhub,hM,hQhub,hQspoke,hQQ,hQM,hE,hS,hQarc⟩:=hfamilyMatch u
  let M:=Finset.univ.image W
  let Pack:=mixedWheelRimPack len M Q
  have hlength:=ordinary_physical_assigned_payload_length F hF π d m RM state L u i₀ Cres assign hsize
  let nlen:=fun a:T=>(C a).length-1
  have hnlen:∀a,2≤nlen a:=by
    intro a
    have hh:3≤(C a).length:=(hcycle a).isCircuit.three_le_length
    dsimp [nlen];omega
  have hlenQ:∀a:T,len a=nlen a+1:=by
    intro a
    have hc:=hClen a
    have ha:=hlength a
    have hh:3≤(C a).length:=(hcycle a).isCircuit.three_le_length
    dsimp [len,nlen]
    omega
  let select:T↪T:=Function.Embedding.refl _
  let Q':∀a:T,OrderedOrdinaryWheel (U:=U) π (3*d) (nlen a+1):=reindexedOrdinaryWheel π (3*d) len Q nlen select hlenQ
  have hQall:=assigned_ordinary_wheels_reindex π (3*d) m (fun e:E=>e.val.1) (fun e:E=>e.val.2)
    (fun e:S=>e.val.1) (fun e:S=>e.val.2) (H false) (H true) len Q nlen select hlenQ u hQhub
    (by intro a i; rw [hQhub a]; exact hQspoke a i) (rawMixedPhysicalArc Host π d raw) hQarc hQQ M
    (by convert hQM using 1 <;> congr! 5 <;>
      (try (ext z; cases z <;> simp [markedWheelPhysicalResources_rim,markedWheelPhysicalResources_spoke])))
  have hC':∀a:T,(C a).length=nlen a+1:=by
    intro a
    have hh:3≤(C a).length:=(hcycle a).isCircuit.three_le_length
    dsimp [nlen];omega
  have hfirst:=ordinary_mixed_source_buffered_embedding_with_coverage (E:=E) (L:=S) (A:=A) (B:=B) (J:=T) (F u) (hF u) Host
    (fun e:E=>e.val.1) (fun e:E=>e.val.2) (fun e:S=>e.val.1) (fun e:S=>e.val.2) π (m+1) d m (by omega) hd rfl hnoshort raw t
  have hdec:ordinaryBufferedCoverageFin n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [hdec] at hfirst
  have hsecond:=hfirst Jret u index
  have hthird:=hsecond u₀ v₀ Paths hp hP hlen ext hsupp hsrc inner hinner root C hcycle hC hcross
  have hfourth:=hthird M hMhub hM nlen hnlen Q' hC'
  have hfifth:=hfourth hQall.1 hQall.2.1 hQall.2.2.2.1
    (by convert hQall.2.2.2.2 using 1 <;> congr! 5 <;>
      (try (ext z; cases z <;> simp [markedWheelPhysicalResources_rim,markedWheelPhysicalResources_spoke])))
  have hsixth:=hfifth (fun e=>(hE e).1) (fun e=>(hS e).1)
    (rawMixedPhysicalArc Host π d raw) (fun e=>(hE e).2) (fun e=>(hS e).2) hQall.2.2.1
  have hMark:∀Z∈M,markedCyclePhysicalEdges (fun e:E=>e.val.1) (fun e:E=>e.val.2) (fun e:S=>e.val.1) (fun e:S=>e.val.2) m π (3*d) Z.1⊆Pack:=by
    classical
    intro Z hZ e he
    simp only [Pack,mixedWheelRimPack,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and]
    left
    refine ⟨Z,hZ,?_⟩
    convert he using 1 <;> congr! 5 <;> (try (ext x; simp [markedCyclePhysicalEdges,markedPhysicalEdge]))
  have hOrd:∀a i,{(Q' a).1.val i,(Q' a).1.val (cycleNext i)}∈Pack:=by
    classical
    intro a i
    simp only [Pack,mixedWheelRimPack,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
    right
    refine ⟨a,Fin.cast (hlenQ a).symm i,?_⟩
    simp only [Q',reindexedOrdinaryWheel,cast_ordinary_wheel_vertex]
    change _ = {(Q a).1.val (Fin.cast (hlenQ a).symm i), (Q a).1.val (Fin.cast (hlenQ a).symm (cycleNext i))}
    rw [cycleNext_cast (hlenQ a)]
    ext x; simp
  exact ⟨W,hW,hsixth Pack hMark hOrd⟩
end Oberwolfach
