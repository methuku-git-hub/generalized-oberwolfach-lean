module

public import Oberwolfach.ActualSelectedPackingPositions
public import Oberwolfach.MixedPackingRunCycleSeparation
public import Oberwolfach.OrdinaryPackedWheelDirectedPathEdges
public import Oberwolfach.PackedRunNonordinaryMarkers
public import Oberwolfach.ActualOldPiecePaths
public import Oberwolfach.ResidualDeletedPathLengths

@[expose] public section
/-! From one physical mixed packing, construct all ordinary-cycle and marked-run
target pieces together, with the same assignment, directions and disjoint supports. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 32000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_mixed_packing_target_pieces_with_wheel_support
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (hc:data.c=m+1)
    (π:Equiv.Perm V) (hb:1≤b) (hπ:∀x,π x≠x) (H₀ Hₖ:V→U→Prop) (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j)))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U)
    (hpack:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hT:∀i∈data.s₂,data.T i=packedMarkedPositions tail head ktail khead m b data.d π H₀ Hₖ M hub (root i))
    (Ord:Finset V) (hOrd:∀W∈M,∀a:Fin (m+1),a.val≠0→W.1.val a∈Ord)
    (havoid:∀i,Disjoint (permutationWindow π 0 data.d (root i)) Ord)
    (n:{j // j∈data.t}→ℕ) (hn:∀j,2≤n j)
    (C:∀j:{j // j∈data.t},OrderedOrdinaryWheel (U:=U) π b (n j+1))
    (hlenC:∀j,(data.C j.val).length=n j+1) (hhubC:∀j,(C j).2=hub)
    (hOrdC:∀j a,(C j).1.val a∈Ord)
    (hCC:∀j k,j≠k→Disjoint (ordinaryWheelPhysicalResources (C j)) (ordinaryWheelPhysicalResources (C k)))
    (hCM:∀j W,W∈M→Disjoint (ordinaryWheelPhysicalResources (C j)) (markedWheelPhysicalResources W))
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:L,G.Adj (ktail e) (π (khead e)))
    (R:V→V→Prop) (hER:∀e:E,R (tail e) (head e)) (hKR:∀e:L,R (ktail e) (π (khead e)))
    (hCR:∀j a,R ((C j).1.val a) ((C j).1.val (cycleNext a))):
    ∃(W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ)
      (u v:actualOldPieceIndex data→V) (q:∀z,(SimpleGraph.completeGraph V).Walk (u z) (v z)),
      (∀z,W z∈M ∧ (W z).2.val=hub ∧ (W z).1.val 0=(π^z.2.val.val) (root z.1.1.val)) ∧
      (∀z,(q z).IsPath) ∧ (∀z,(q z).length=(actualOldPieceWalk data z).length) ∧
      (∀z z',z≠z'→Disjoint (q z).support.toFinset (q z').support.toFinset) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,u (.inr r)=(π^r.2.val.1) (root r.1.val)) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,v (.inr r)=(π^(r.2.val.2+1)) (root r.1.val)) ∧
      (∀j:{j // j∈data.t},∀x∈(q (.inl j)).support,x∈Ord) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀x∈(q (.inr r)).support,x∉Ord→
        ∃j:Fin (data.d+1),r.2.val.1≤j.val ∧ j.val≤r.2.val.2+1 ∧ x=(π^j.val) (root r.1.val)) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
        (q (.inr r)).getVert (data.c*j)=(π^(r.2.val.1+j)) (root r.1.val)) ∧
      (∀j:{j // j∈data.t},u (.inl j)=(C j).1.val (cycleNext 0) ∧ v (.inl j)=(C j).1.val 0) ∧
      (∀j:{j // j∈data.t},R (v (.inl j)) (u (.inl j))) ∧
      (∀j:{j // j∈data.t},∀k,k<(q (.inl j)).length→∃a:Fin (n j+1),
        (q (.inl j)).getVert k=(C j).1.val a ∧ (q (.inl j)).getVert (k+1)=(C j).1.val (cycleNext a)) ∧
      (∀z k,k<(q z).length→R ((q z).getVert k) ((q z).getVert (k+1))) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀e:Sym2 V,e∈(q (.inr r)).edges→∃z:actualSelectedSegmentIndex data,z.1=r ∧
        e.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1) ∧
      (∀z:actualSelectedSegmentIndex data,∀i:Fin (m+1),(W z).1.val i∈(q (.inr z.1)).support):=by
  obtain ⟨W,hW,hWW⟩:=actual_selected_segments_choose_wheels_from_packing_positions data tail head ktail khead m b π H₀ Hₖ root hinj hdis M hub hpack hT
  have hw:∀z,(W z).2.val=hub ∧ (W z).1.val 0=(π^z.2.val.val) (root z.1.1.val):=fun z=>⟨(hW z).2.1,(hW z).2.2⟩
  have hwo:∀z (a:Fin (m+1)),a.val≠0→(W z).1.val a∈Ord:=fun z=>hOrd (W z) (hW z).1
  obtain ⟨qr,hqr,hrr⟩:=actual_selected_run_family_from_packed_wheels data G tail head ktail khead m b hc π hb hπ H₀ Hₖ root hinj hdis W hub hw hWW Ord hwo havoid hE hK R hER hKR
  have hex:∀j:{j // j∈data.t},∃p:(SimpleGraph.completeGraph V).Walk ((C j).1.val (cycleNext 0)) ((C j).1.val 0),
      p.IsPath ∧ p.length=n j ∧ p.support.toFinset=Finset.univ.image (C j).1.val ∧
      R ((C j).1.val 0) ((C j).1.val (cycleNext 0)) ∧
      (∀k,k<p.length→∃a:Fin (n j+1),p.getVert k=(C j).1.val a ∧ p.getVert (k+1)=(C j).1.val (cycleNext a)) ∧
      (∀k,k<p.length→R (p.getVert k) (p.getVert (k+1))):=by
    intro j
    exact ordinary_packed_wheel_directed_path_with_edges π b (n j) (hn j) (C j) R (hCR j)
  choose qc hqc using hex
  let u:actualOldPieceIndex data→V
    | .inl j=>(C j).1.val (cycleNext 0)
    | .inr r=>(π^r.2.val.1) (root r.1.val)
  let v:actualOldPieceIndex data→V
    | .inl j=>(C j).1.val 0
    | .inr r=>(π^(r.2.val.2+1)) (root r.1.val)
  let q:∀z,(SimpleGraph.completeGraph V).Walk (u z) (v z)
    | .inl j=>qc j
    | .inr r=>qr r
  have hcross:∀j r,Disjoint (qc j).support.toFinset (qr r).support.toFinset:=by
    intro j r
    rw [(hqc j).2.2.1]
    apply actual_packed_run_avoids_ordinary_rim data tail head ktail khead m b (n j+1) π H₀ Hₖ root W (C j)
      (fun z=>(hhubC j).trans (hw z).1.symm) (fun z=>hCM j (W z) (hW z).1) Ord (hOrdC j) havoid r (qr r)
    exact fun x hx=>((hqr r).2.2.1 x).mp hx
  have hqdis:∀z z':actualOldPieceIndex data,z≠z'→Disjoint (q z).support.toFinset (q z').support.toFinset:=by
    intro z z' hne
    cases z with
    | inl j =>
      cases z' with
      | inl k =>
        change Disjoint (qc j).support.toFinset (qc k).support.toFinset
        rw [(hqc j).2.2.1,(hqc k).2.2.1]
        exact ordinary_packed_rims_disjoint (C j) (C k) ((hhubC j).trans (hhubC k).symm) (hCC j k (fun he=>hne (congrArg Sum.inl he)))
      | inr r =>exact hcross j r
    | inr r =>
      cases z' with
      | inl j =>exact (hcross j r).symm
      | inr s =>exact hrr r s (fun he=>hne (congrArg Sum.inr he))
  refine ⟨W,u,v,q,hW,?_,?_,hqdis,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z;cases z with | inl j=>exact (hqc j).1 | inr r=>exact (hqr r).1
  · intro z;cases z with
    | inl j =>
      change (qc j).length=(data.C j.val).tail.length
      rw [(hqc j).2.1,SimpleGraph.Walk.length_tail,hlenC j]
      omega
    | inr r =>
      change (qr r).length=(data.path (.inr r)).length
      rw [(hqr r).2.1]
      exact ((deleted_path_lengths F data.s₁ data.s₂ data.u data.v data.P data.hp data.c data.d
        (lt_of_lt_of_le (by decide:0<3) data.hc) data.hlen data.T (fun i _=>data.hT i)).2 r.1 r.2).symm
  · intro r;rfl
  · intro r;rfl
  · intro j x hx
    have hm:x∈Finset.univ.image (C j).1.val:=by
      rw [←(hqc j).2.2.1];exact List.mem_toFinset.mpr hx
    obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hm
    rw [←ha];exact hOrdC j a
  · intro r x hx hn'
    exact packed_run_nonordinary_label_is_marker data tail head ktail khead m b π H₀ Hₖ root W (fun z=>(hw z).2) Ord hwo r (qr r)
      (fun x hx=>((hqr r).2.2.1 x).mp hx) x hx hn'
  · intro r j hj;exact (hqr r).2.2.2.1 j hj
  · intro j;exact ⟨rfl,rfl⟩
  · intro j;exact (hqc j).2.2.2.1
  · intro j;exact (hqc j).2.2.2.2.1
  · intro z;cases z with | inl j=>exact (hqc j).2.2.2.2.2 | inr r=>exact (hqr r).2.2.2.2.2
  · intro r e he;exact (hqr r).2.2.2.2.1 e he
  · intro z i
    exact ((hqr z.1).2.2.1 _).mpr (Or.inr ⟨z,rfl,i,rfl⟩)
end Oberwolfach
