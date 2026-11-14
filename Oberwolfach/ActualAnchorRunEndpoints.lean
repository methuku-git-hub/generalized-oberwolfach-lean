module

public import Oberwolfach.ActualParentBufferedMarker

@[expose] public section
/-! The prescribed anchor map sends each selected-run endpoint to its
original interval endpoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_anchor_values_on_run_endpoints
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [Fintype K] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (π:Equiv.Perm V) (root:K→V) (g:{x // x∈data.prescribed}↪V)
    (hg:∀i (j:Fin (data.d+1)) (hj:bufferedMarker data.c data.d (ext i) j∈data.prescribed),
      g ⟨bufferedMarker data.c data.d (ext i) j,hj⟩=(π^j.val) (root i)):
    (∀r:SelectedRunIndex data.s₂ data.d data.T,∀hp:data.start (.inr r)∈data.prescribed,
      g ⟨data.start (.inr r),hp⟩=(π^r.2.val.1) (root r.1.val)) ∧
    (∀r:SelectedRunIndex data.s₂ data.d data.T,∀hp:data.finish (.inr r)∈data.prescribed,
      g ⟨data.finish (.inr r),hp⟩=(π^(r.2.val.2+1)) (root r.1.val)):=by
  have hbound:∀r:SelectedRunIndex data.s₂ data.d data.T,r.2.val.1≤data.d ∧ r.2.val.2+1≤data.d:=by
    intro r
    have hr:=(selected_run_mem data.d (data.T r.1.val) (data.hT r.1.val) r.2.val.1 r.2.val.2).mp r.2.property
    have hlast:=data.hT r.1.val (hr.2.1 r.2.val.2 hr.1 le_rfl)
    have hb:r.2.val.2<data.d:=Finset.mem_range.mp hlast
    exact ⟨le_trans hr.1 (Nat.le_of_lt hb),Nat.succ_le_of_lt hb⟩
  constructor
  · intro r hp
    let j:Fin (data.d+1):=⟨r.2.val.1,by have hh:=(hbound r).1;omega⟩
    have hs:data.start (.inr r)=bufferedMarker data.c data.d (ext r.1.val) j:=by
      change (data.P r.1.val).getVert (2+data.c*r.2.val.1)=bufferedMarker data.c data.d (ext r.1.val) j
      exact actual_parent_buffered_marker data ext hsupp r.1.val (Finset.mem_union_right _ r.1.property) j
    have hp':bufferedMarker data.c data.d (ext r.1.val) j∈data.prescribed:=by rw [←hs];exact hp
    have hh:=hg r.1.val j hp'
    simpa only [←hs] using hh
  · intro r hp
    let j:Fin (data.d+1):=⟨r.2.val.2+1,by have hh:=(hbound r).2;omega⟩
    have hs:data.finish (.inr r)=bufferedMarker data.c data.d (ext r.1.val) j:=by
      change (data.P r.1.val).getVert (2+data.c*(r.2.val.2+1))=bufferedMarker data.c data.d (ext r.1.val) j
      exact actual_parent_buffered_marker data ext hsupp r.1.val (Finset.mem_union_right _ r.1.property) j
    have hp':bufferedMarker data.c data.d (ext r.1.val) j∈data.prescribed:=by rw [←hs];exact hp
    have hh:=hg r.1.val j hp'
    simpa only [←hs] using hh
end Oberwolfach
