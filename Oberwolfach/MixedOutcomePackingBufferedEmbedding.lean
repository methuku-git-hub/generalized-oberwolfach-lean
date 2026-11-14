module

public import Oberwolfach.ActualMixedPackingBufferedEmbedding
public import Oberwolfach.MixedOutcomeOrdinarySpokeExclusion
public import Oberwolfach.RawMarkedWheelOrdinarySpokes
public import Oberwolfach.PackedPhysicalSpokePositions

@[expose] public section
/-! Derive the interval geometry, ordinary-spoke exclusion and physical
selected-position matching from the same raw interval outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 36000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_outcome_physical_packing_buffered_embedding
    {X V U E L K J I Γ Color:Type} [Fintype X] [DecidableEq X] [Fintype V] [LinearOrder V] [Nonempty V]
    [Fintype U] [DecidableEq U] [Fintype K] [DecidableEq K] [DecidableEq J] [Fintype I] [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (hc:data.c=m+1)
    (π:Equiv.Perm V) (hb:1≤b) (hnoshort:∀x l,0<l→l<2*data.d+1→(π^l) x≠x)
    (σ:RawMarkedOutcome V U Γ Color) (g₀ g₁:Γ) (hclasses:g₀≠g₁) (color:Color) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π data.d (fun e=>σ (Sum.inr e)) g₀) t) (w:U)
    (index:K ≃ retainedAndRawIntervalIndex π data.d (fun e=>σ (Sum.inr e)) g₀ g₁ t Jret w):
    ∀(M:Finset (MarkedWheel tail head ktail khead m π b (rawMarkedPairSpokes π data.d σ g₁ color false) (rawMarkedPairSpokes π data.d σ g₁ color true))),
    (∀W∈M,W.2.val=w)→
    (∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))→
    (∀i∈data.s₂,data.T i=packedPhysicalSpokePositions tail head ktail khead m b data.d π (rawMarkedPairSpokes π data.d σ g₁ color false) (rawMarkedPairSpokes π data.d σ g₁ color true) M w ((fun i=>retainedAndRawIntervalRoot π data.d (fun e=>σ (Sum.inr e)) g₀ g₁ t Jret w (index i)) i))→
    ∀(n:{j // j∈data.t}→ℕ), (∀j,2≤n j)→
    ∀(C:∀j:{j // j∈data.t},OrderedOrdinaryWheel (U:=U) π b (n j+1)),
    (∀j,(data.C j.val).length=n j+1)→(∀j,(C j).2=w)→
    (∀j a,(rawMarkedPairSpokes π data.d σ g₁ color false) ((C j).1.val a) w)→
    (∀j k,j≠k→Disjoint (ordinaryWheelPhysicalResources (C j)) (ordinaryWheelPhysicalResources (C k)))→
    (∀j W,W∈M→Disjoint (ordinaryWheelPhysicalResources (C j)) (markedWheelPhysicalResources W))→
    (∀e:E,G.Adj (tail e) (head e))→(∀e:L,G.Adj (ktail e) (π (khead e)))→
    ∀(R:V→V→Prop), (∀e:E,R (tail e) (head e))→(∀e:L,R (ktail e) (π (khead e)))→
    (∀j a,R ((C j).1.val a) ((C j).1.val (cycleNext a)))→
    F.IsRegularOfDegree 2→(data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)→
    ∀(ext:∀i:K,Fin (data.c*data.d+5)↪X),
    (∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))→
    (∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))→
    ∀(bidx:I≃{i // i∈data.s₁}) (finalExt:∀i:I,Fin (data.c*data.d+5)↪X)
      (inner:∀i:I,Fin (data.c*data.d+1)↪X),
    (∀i p,inner i p=finalExt i ⟨p.val+2,by omega⟩)→
    (∀i,(data.P (bidx i).val).support=List.ofFn (finalExt i))→
    ∃(W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b (rawMarkedPairSpokes π data.d σ g₁ color false) (rawMarkedPairSpokes π data.d σ g₁ color true))
      (u v:actualOldPieceIndex data→V) (q:∀z,(SimpleGraph.completeGraph V).Walk (u z) (v z))
      (g:{x // x∈data.prescribed}↪V) (f:{x // x∈(Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset))}↪V) (ψ:X→V),
      (∀z,W z∈M ∧ (W z).2.val=w ∧ (W z).1.val 0=(π^z.2.val.val) ((fun i=>retainedAndRawIntervalRoot π data.d (fun e=>σ (Sum.inr e)) g₀ g₁ t Jret w (index i)) z.1.1.val)) ∧
      (∀z,(q z).IsPath) ∧ (∀z,(q z).length=(actualOldPieceWalk data z).length) ∧
      (∀z z',z≠z'→Disjoint (q z).support.toFinset (q z').support.toFinset) ∧
      (∀i (j:Fin (data.d+1)) (hj:bufferedMarker data.c data.d (ext i) j∈data.prescribed),
        g ⟨bufferedMarker data.c data.d (ext i) j,hj⟩=(π^j.val) ((fun i=>retainedAndRawIntervalRoot π data.d (fun e=>σ (Sum.inr e)) g₀ g₁ t Jret w (index i)) i)) ∧
      (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
        f ⟨(actualOldPieceWalk data z).getVert k.val,
          Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
          (q z).getVert k.val) ∧
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner):Set X) ∧
      (∀x (hx:x∈(Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset))),ψ x=f ⟨x,hx⟩) ∧ (∀x (hx:x∈data.prescribed),ψ x=g ⟨x,hx⟩) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
        ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) ((fun i=>retainedAndRawIntervalRoot π data.d (fun e=>σ (Sum.inr e)) g₀ g₁ t Jret w (index i)) r.1.val)) ∧
      (∀j:{j // j∈data.t},u (.inl j)=(C j).1.val (cycleNext 0) ∧ v (.inl j)=(C j).1.val 0) ∧
      (∀j:{j // j∈data.t},R (v (.inl j)) (u (.inl j))) ∧
      (∀j:{j // j∈data.t},∀k,k<(q (.inl j)).length→∃a:Fin (n j+1),
        (q (.inl j)).getVert k=(C j).1.val a ∧ (q (.inl j)).getVert (k+1)=(C j).1.val (cycleNext a)) ∧
      (∀z k,k<(q z).length→R ((q z).getVert k) ((q z).getVert (k+1))) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀e:Sym2 V,e∈(q (.inr r)).edges→∃z:actualSelectedSegmentIndex data,z.1=r ∧
        e.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1):=by
  intro M hMhub hpack hT n hn C hlenC hhubC hCr hCC hCM hE hK R hER hKR hCR hF hCycle ext hsupp hsrc bidx finalExt inner hinner hfinal
  let root:=fun i=>retainedAndRawIntervalRoot π data.d (fun e=>σ (Sum.inr e)) g₀ g₁ t Jret w (index i)
  let H₀:=rawMarkedPairSpokes π data.d σ g₁ color false
  let Hₖ:=rawMarkedPairSpokes π data.d σ g₁ color true
  let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
  let Ord:=rawIntervalOrdinaryOuter π data.d (fun e=>σ (Sum.inr e)) color w
  have hgeom:=retained_and_raw_interval_geometry π data.d data.hd hnoshort (fun e=>σ (Sum.inr e)) g₀ g₁ hclasses t Jret w
  have hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)):=fun i=>hgeom.1 (index i)
  have hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j)):=
    fun i j hij=>hgeom.2 (index i) (index j) (fun he=>hij (index.injective he))
  have havoid:∀i,Disjoint (permutationWindow π 0 data.d (root i)) Ord:=by
    intro i
    exact retained_and_raw_intervals_avoid_ordinary_spokes π data.d (fun e=>σ (Sum.inr e)) g₀ g₁ t Jret w color (index i)
  have hOrd:∀W∈M,∀a:Fin (m+1),a.val≠0→W.1.val a∈Ord:=by
    intro W hW a ha
    exact raw_marked_wheel_nonroot_spokes_ordinary tail head ktail khead π data.d m b σ g₁ color W w (hMhub W hW) a ha
  have hT':∀i∈data.s₂,data.T i=packedMarkedPositions tail head ktail khead m b data.d π H₀ Hₖ M w (root i):=by
    intro i hi
    rw [hT i hi]
    exact packed_physical_spoke_positions_eq_marked_roots tail head ktail khead m b data.d π H₀ Hₖ M w (root i) Ord
      (fun W hW _ a ha=>hOrd W hW a ha) (havoid i)
  have hOrdC:∀j a,(C j).1.val a∈Ord:=by
    intro j a
    simpa only [Ord,rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and,rawMarkedPairSpokes,rawMarkedSpokes] using hCr j a
  have hπ:∀x,π x≠x:=by
    intro x
    simpa only [pow_one] using hnoshort x 1 (by omega) (by have hh:=data.hd;omega)
  exact actual_mixed_packing_buffered_embedding data G tail head ktail khead m b hc π hb hπ H₀ Hₖ root hinj hdis M w hpack hT' Ord hOrd havoid n hn C hlenC hhubC hOrdC hCC hCM hE hK R hER hKR hCR hF hCycle ext hsupp hsrc bidx finalExt inner hinner hfinal
end Oberwolfach
