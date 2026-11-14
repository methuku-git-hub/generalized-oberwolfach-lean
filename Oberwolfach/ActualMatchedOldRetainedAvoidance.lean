module

public import Oberwolfach.ActualOldAvoidanceFromPieces
public import Oberwolfach.ActualMatchedPieceAvoidance
public import Oberwolfach.RetainedRawIntervalLabelAvoidance

@[expose] public section
/-! The matching-built old embedding avoids retained marked roots outside
the final buffered source paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_old_avoids_retained_roots
    {X V U K J I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [Fintype U] [DecidableEq U] [Fintype K] [DecidableEq K] [DecidableEq J] [Fintype I]
    {G:SimpleGraph X} (hG:G.IsRegularOfDegree 2)
    (data:ActualResidualData (K:=K) (J:=J) G)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (b:I≃{i // i∈data.s₁}) (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i k,inner i k=ext (b i).val ⟨k.val+2,by omega⟩)
    (hactive:∀i:K,i∈data.s₁∨i∈data.s₂)
    (π:Equiv.Perm V) (hnoshort:∀x l,0<l→l<2*data.d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π data.d σ false) t) (w:U)
    (index:K ≃ retainedAndRawIntervalIndex π data.d σ false true t Jret w)
    (happrox:∀i∈data.s₂,∃a:{a:V // rawIntervalColouredStart π data.d (fun e=>σ (w,e)) a true},index i=Sum.inr a)
    (H:SimpleGraph V) (u v:actualOldPieceIndex data→V) (q:∀z,H.Walk (u z) (v z)):
    let root:=fun i=>retainedAndRawIntervalRoot π data.d σ false true t Jret w (index i)
    let Ord:=rawIntervalOrdinaryOuter π data.d σ true w
    let Y:=markedIntervalRootSet π (fun _:retainedMarkedIndex π data.d σ false t Jret w=>data.d) Subtype.val
    (∀j:{j // j∈data.t},∀x∈(q (.inl j)).support,x∈Ord)→
    (∀r:SelectedRunIndex data.s₂ data.d data.T,∀x∈(q (.inr r)).support,x∉Ord→
      ∃j:Fin (data.d+1),r.2.val.1≤j.val ∧ j.val≤r.2.val.2+1 ∧ x=(π^j.val) (root r.1.val))→
    ∀(ψ:X→V),
    (∀i (j:Fin (data.d+1)),bufferedMarker data.c data.d (ext i) j∈data.prescribed→
      ψ (bufferedMarker data.c data.d (ext i) j)=(π^j.val) (root i))→
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V),
    (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩)→
    (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
        (q z).getVert k.val)→
    ∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>data.c*data.d) inner→ψ x∉Y:=by
  intro root Ord Y hcycle hrun ψ hpres A f hψ hf
  have hgeom:=retained_labels_avoid_ordinary_and_raw_intervals π data.d (by have hh:=data.hd;omega)
    hnoshort σ false true (by decide) t Jret w true
  have hwindow:∀i∈data.s₂,∀j:Fin (data.d+1),(π^j.val) (root i)∉Y:=by
    intro i hi j
    obtain ⟨a,ha⟩:=happrox i hi
    have hh:=hgeom.2 a j
    simpa only [root,ha,retainedAndRawIntervalRoot] using hh
  have hpiece:=actual_matched_pieces_avoid_reserved_labels data π root Ord Y H u v q hcycle hrun hgeom.1 hwindow ψ f hψ hf
  apply actual_old_outside_final_avoids_reserved_set hG data hCycle ext hsupp b inner hinner hactive ψ Y
  · intro i hi j hj
    rw [hpres i j hj]
    exact hwindow i hi j
  · exact hpiece
end Oberwolfach
