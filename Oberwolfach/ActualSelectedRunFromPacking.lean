module

public import Oberwolfach.ActualSelectedPackingPositions
public import Oberwolfach.MarkedPackedOrbitDirectedEdges

@[expose] public section
/-! A selected actual maximal run is realised by the corresponding original
packed marked wheels, preserving its interval markers and physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_run_from_packed_wheels
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (G:SimpleGraph V) (tail head:E → V) (ktail khead:L → V) (m b:ℕ) (hc:data.c=m+1)
    (π:Equiv.Perm V) (hb:1≤b) (hπ:∀x,π x≠x) (H₀ Hₖ:V → U → Prop) (root:K → V)
    (hinj:∀ i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (W:actualSelectedSegmentIndex data → MarkedWheel tail head ktail khead m π b H₀ Hₖ) (hub:U)
    (hW:∀z,(W z).2.val=hub ∧ (W z).1.val 0=(π^z.2.val.val) (root z.1.1.val))
    (hpair:∀z z',z≠z' → Disjoint (markedWheelPhysicalResources (W z)) (markedWheelPhysicalResources (W z')))
    (Ord:Finset V) (hOrd:∀z (a:Fin (m+1)),a.val≠0 → (W z).1.val a∈Ord)
    (r:SelectedRunIndex data.s₂ data.d data.T)
    (havoid:(π^(r.2.val.2+1)) (root r.1.val)∉Ord)
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:L,G.Adj (ktail e) (π (khead e)))
    (R:V → V → Prop) (hER:∀e:E,R (tail e) (head e)) (hKR:∀e:L,R (ktail e) (π (khead e))):
    let a:=r.2.val.1
    let b':=r.2.val.2
    ∃q:(SimpleGraph.completeGraph V).Walk ((π^a) (root r.1.val)) ((π^(b'+1)) (root r.1.val)),
      q.IsPath ∧ q.length=data.c*(b'+1-a) ∧
      (∀x,x∈q.support ↔ x=(π^(b'+1)) (root r.1.val) ∨
        ∃z:actualSelectedSegmentIndex data,z.1=r ∧ ∃i:Fin (m+1),(W z).1.val i=x) ∧
      (∀ j,j≤b'+1-a → q.getVert (data.c*j)=(π^(a+j)) (root r.1.val)) ∧
      (∀e:Sym2 V,e∈q.edges → ∃z:actualSelectedSegmentIndex data,z.1=r ∧
        e.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1) ∧
      (∀ k,k<q.length → R (q.getVert k) (q.getVert (k+1))):=by
  classical
  intro a b'
  have hr:=(selected_run_mem data.d (data.T r.1.val) (data.hT r.1.val) r.2.val.1 r.2.val.2).mp r.2.property
  have hlast:=data.hT r.1.val (hr.2.1 r.2.val.2 hr.1 le_rfl)
  have hbnd:b'+1≤data.d:=by have hh:=Finset.mem_range.mp hlast;omega
  let n:=b'+1-a
  have hab:a+n=b'+1:=by dsimp [n,a,b'];have hh:=hr.1;omega
  have hbound:a+n≤data.d:=by rw [hab];exact hbnd
  let z (i:ℕ) (hi:a ≤ i) (hj:i < a+n):actualSelectedSegmentIndex data:=
    ⟨r,⟨⟨i,by have hh:=hbound;omega⟩,⟨hi,by change i≤r.2.val.2;have hh:=hab;dsimp only [b'] at hh;omega⟩⟩⟩
  let Wr (i:ℕ) (hi:a ≤ i) (hj:i < a+n):=W (z i hi hj)
  have hwroot:∀ i (hi:a ≤ i) (hj:i < a+n),(Wr i hi hj).1.val 0=(π^i) (root r.1.val):=by
    intro i hi hj
    exact (hW (z i hi hj)).2
  have hwdis:∀ i j (hi:a ≤ i) (hj:i < a+n) (hi':a ≤ j) (hj':j < a+n),i≠j → 
      Disjoint (markedWheelPhysicalResources (Wr i hi hj)) (markedWheelPhysicalResources (Wr j hi' hj')):=by
    intro i j hi hj hi' hj' hij
    apply hpair
    intro he
    have hv:=congrArg (fun z:actualSelectedSegmentIndex data=>z.2.val.val) he
    exact hij hv
  have hwhub:∀ i j (hi:a ≤ i) (hj:i < a+n) (hi':a ≤ j) (hj':j < a+n),
      (Wr i hi hj).2.val=(Wr j hi' hj').2.val:=by
    intro i j hi hj hi' hj'
    exact (hW (z i hi hj)).1.trans (hW (z j hi' hj')).1.symm
  have hword:∀ i (hi:a ≤ i) (hj:i < a+n) (k:Fin (m+1)),k.val≠0 → (Wr i hi hj).1.val k∈Ord:=by
    intro i hi hj k hk
    exact hOrd (z i hi hj) k hk
  have havo':(π^(a+n)) (root r.1.val)∉Ord:=by rw [hab];exact havoid
  obtain ⟨q,hq,hlen,hmem,hmarks,hedges,hdir⟩:=packed_marked_wheels_form_orbit_run_with_edges G tail head ktail khead m b π hb H₀ Hₖ
    (root r.1.val) data.d a n hbound hπ (hinj r.1.val) Wr hwroot hwdis hwhub Ord hword havo' hE hK R hER hKR
  have hresult:∃q:(SimpleGraph.completeGraph V).Walk ((π^a) (root r.1.val)) ((π^(a+n)) (root r.1.val)),
      q.IsPath ∧ q.length=data.c*n ∧
      (∀x,x∈q.support ↔ x=(π^(a+n)) (root r.1.val) ∨
        ∃z:actualSelectedSegmentIndex data,z.1=r ∧ ∃i:Fin (m+1),(W z).1.val i=x) ∧
      (∀ j,j≤n → q.getVert (data.c*j)=(π^(a+j)) (root r.1.val)) ∧
      (∀e:Sym2 V,e∈q.edges → ∃z:actualSelectedSegmentIndex data,z.1=r ∧
        e.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1) ∧
      (∀ k,k<q.length → R (q.getVert k) (q.getVert (k+1))):=by
    refine ⟨q,hq,?_,?_,?_,?_,hdir⟩
    · simpa [hc,Nat.mul_comm] using hlen
    · intro x
      rw [hmem x]
      constructor
      · rintro (h|⟨i,hi,hj,k,hk⟩)
        · exact Or.inl h
        · exact Or.inr ⟨z i hi hj,rfl,k,hk⟩
      · rintro (h|⟨z',hz',k,hk⟩)
        · exact Or.inl h
        · rcases z' with ⟨s,⟨j,hj⟩⟩
          change s=r at hz'
          subst s
          have hlo:a ≤ j.val:=hj.1
          have hhi:j.val<a+n:=by have hh:=hj.2;rw [hab];dsimp [b'];omega
          right
          refine ⟨j.val,hlo,hhi,k,?_⟩
          exact hk
    · intro j hj
      simpa only [hc] using hmarks j hj
    · intro e he
      obtain ⟨i,hi,hj,he⟩:=hedges e he
      exact ⟨z i hi hj,rfl,he⟩
  rw [←hab]
  simpa only [Nat.add_sub_cancel_left] using hresult
end Oberwolfach
