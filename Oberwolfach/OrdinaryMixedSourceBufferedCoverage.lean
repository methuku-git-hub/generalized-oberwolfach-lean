module

public import Oberwolfach.MixedOutcomePackingBufferedSupport
public import Oberwolfach.ActualResidualDataFromPacking
public import Oberwolfach.ActualOldImageDirected
public import Oberwolfach.ActualOldPhysicalCoverage
public import Oberwolfach.ActualMatchedPiecePhysicalEdges

@[expose] public section
/-! Extend the interval-marker map over the matched short cycles and the
selected path runs, for any physically disjoint mixed wheel family on the
same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryBufferedCoverageFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_mixed_source_buffered_embedding_with_coverage
    {N:ℕ} {U X E L A B J:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    [Fintype E] [Fintype L] [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq J] [Nonempty (Fin N)]
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2) (G:SimpleGraph (Fin N))
    (tail head:E→Fin N) (ktail khead:L→Fin N)
    (π:Equiv.Perm (Fin N)) (c d m:ℕ) (hc:3≤c) (hd:0<d) (hcm:c=m+1)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin N) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (w:U)
    (index:A⊕B ≃ retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t Jret w)
    (u v:A⊕B→X) (P:∀i,F.Walk (u i) (v i)) (hp:∀i,(P i).IsPath)
    (hP:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
    (hlen:∀i,(P i).length=c*d+4) (ext:∀i:A⊕B,Fin (c*d+5)↪X)
    (hsupp:∀i,(P i).support=List.ofFn (ext i))
    (hsrc:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (inner:∀a:A,Fin (c*d+1)↪X) (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (root:J→X) (C:∀j,F.Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hC:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset)
    (M:Finset (MarkedWheel tail head ktail khead m π (3*d)
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)))
    (hMhub:∀W∈M,W.2.val=w)
    (hM:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (n:J→ℕ) (hn:∀j,2≤n j) (Q:∀j,OrderedOrdinaryWheel (U:=U) π (3*d) (n j+1))
    (hQlen:∀j,(C j).length=n j+1) (hQhub:∀j,(Q j).2=w)
    (hQspoke:∀j a,rawMarkedPairSpokes π d raw true true false ((Q j).1.val a) w)
    (hQQ:∀j k,j≠k→Disjoint (ordinaryWheelPhysicalResources (Q j)) (ordinaryWheelPhysicalResources (Q k)))
    (hQM:∀j W,W∈M→Disjoint (ordinaryWheelPhysicalResources (Q j)) (markedWheelPhysicalResources W))
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:L,G.Adj (ktail e) (π (khead e)))
    (Arc:Fin N→Fin N→Prop) (hER:∀e:E,Arc (tail e) (head e))
    (hKR:∀e:L,Arc (ktail e) (π (khead e)))
    (hQR:∀j a,Arc ((Q j).1.val a) ((Q j).1.val (cycleNext a)))
    (Pack:Finset (Finset (Fin N)))
    (hMarkPack:∀W∈M,markedCyclePhysicalEdges tail head ktail khead m π (3*d) W.1⊆Pack)
    (hOrdPack:∀j a,{(Q j).1.val a,(Q j).1.val (cycleNext a)}∈Pack):
    let targetRoot:=fun i=>retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w (index i)
    let data:=actualResidualDataFromPacking F u v P hp hP c d hc hd hlen tail head ktail khead m (3*d) π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) M w targetRoot root C hcycle hC hcross;
    ∃ψ:X→Fin N,
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner):Set X) ∧
      (∀i (j:Fin (d+1)),bufferedMarker c d (ext i) j∈data.prescribed→
        ψ (bufferedMarker c d (ext i) j)=(π^j.val) (targetRoot i)) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
        ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) (targetRoot r.1.val)) ∧
      ActualOldImageDirected data ψ Arc ∧ ActualOldPhysicalCoverage data ψ Pack :=by
  intro targetRoot data
  let n':{j // j∈data.t}→ℕ:=fun j=>n j.val
  let Q':∀j:{j // j∈data.t},OrderedOrdinaryWheel (U:=U) π (3*d) (n' j+1):=fun j=>Q j.val
  have hpairs:∀j k:{j // j∈data.t},j≠k→Disjoint (ordinaryWheelPhysicalResources (Q' j)) (ordinaryWheelPhysicalResources (Q' k)):=by
    intro j k hjk
    exact hQQ j.val k.val (fun he=>hjk (Subtype.ext he))
  have hT:∀i∈data.s₂,data.T i=packedPhysicalSpokePositions tail head ktail khead m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) M w (targetRoot i):=by
    intro i hi
    rfl
  have hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed:=Finset.Subset.rfl
  have hb:1≤3*d:=by omega
  have hfin:∀i,(data.P ((firstSumIndexEquiv (B:=B)) i).val).support=List.ofFn (ext (.inl i)):=by
    intro i
    exact hsupp (.inl i)
  have hfirst:=mixed_outcome_physical_packing_buffered_embedding_with_support (I:=A) data G tail head ktail khead m (3*d) hcm π hb hnoshort raw false true (by decide) true
  have hsecond:=hfirst t Jret w index
  have hthird:=hsecond M hMhub hM hT
  have hfourth:=hthird n' (fun j=>hn j.val) Q' (fun j=>hQlen j.val) (fun j=>hQhub j.val) (fun j a=>hQspoke j.val a) hpairs
  have hfifth:=hfourth (fun j W hW=>hQM j.val W hW) hE hK Arc hER hKR (fun j a=>hQR j.val a) hF hCycle
  obtain ⟨W,u',v',q,g,f,ψ,hW,hq,hqLen,hqDis,hcy,hrun,hg,hf,hψ,hψf,hψg,hparent,htarget,hclose,hcedges,hdir,hedges⟩:=
    hfifth ext (fun i _=>hsupp i) hsrc firstSumIndexEquiv (fun a=>ext (.inl a)) inner hinner hfin
  have ⟨hpieces,hfirst⟩:=actual_matched_piece_directed_arcs data (SimpleGraph.completeGraph (Fin N)) u' v' q hqLen
    Arc hdir hclose ψ f hψf hf
  have hcycles:=actual_matched_cycle_directed_arcs data ψ Arc hpieces hfirst
  have hruns:∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      Arc (ψ ((data.path (.inr r)).getVert k)) (ψ ((data.path (.inr r)).getVert (k+1))):=by
    intro r k hk
    exact hpieces (.inr r) k hk
  have hWp:∀z,markedCyclePhysicalEdges tail head ktail khead m π (3*d) (W z).1⊆Pack:=
    fun z=>hMarkPack (W z) (hW z).1
  have hCp:∀j a,{(Q' j).1.val a,(Q' j).1.val (cycleNext a)}∈Pack:=fun j a=>hOrdPack j.val a
  have ⟨hpiecesPhysical,hcyclePhysical⟩:=actual_matched_piece_physical_edges_from_wheels data tail head ktail khead m (3*d) π
    (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) W n' Q' u' v' q hqLen htarget hcedges hedges Pack hCp hWp ψ f hψf hf
  have hphysical:ActualOldPhysicalCoverage data ψ Pack:=by
    refine ⟨hcyclePhysical,?_⟩
    intro r k hk
    exact hpiecesPhysical (.inr r) k hk
  refine ⟨ψ,hψ,?_,hparent,⟨hcycles,hruns⟩,hphysical⟩
  intro i j hj
  rw [hψg _ hj]
  exact hg i j hj
end Oberwolfach
