module

public import Oberwolfach.ActualOldPieceTargetMatching

@[expose] public section
/-! Matching the original old pieces transfers every directed target arc,
including the first arc of each cyclic component, back to its source arc. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_piece_directed_arcs
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (H:SimpleGraph V) (u v:actualOldPieceIndex data→V) (q:∀z,H.Walk (u z) (v z))
    (hlen:∀z,(q z).length=(actualOldPieceWalk data z).length)
    (R:V→V→Prop) (hdir:∀z k,k<(q z).length→R ((q z).getVert k) ((q z).getVert (k+1)))
    (hclose:∀j:{j // j∈data.t},R (v (.inl j)) (u (.inl j)))
    (ψ:X→V):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V),
    (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩)→
    (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
        (q z).getVert k.val)→
    (∀z k,k<(actualOldPieceWalk data z).length→
      R (ψ ((actualOldPieceWalk data z).getVert k)) (ψ ((actualOldPieceWalk data z).getVert (k+1)))) ∧
    (∀j:{j // j∈data.t},R (ψ (data.root j.val)) (ψ (data.C j.val).snd)):=by
  intro A f hψ hf
  have hmap:∀z k,k≤(actualOldPieceWalk data z).length→ψ ((actualOldPieceWalk data z).getVert k)=(q z).getVert k:=by
    intro z k hk
    have hx:(actualOldPieceWalk data z).getVert k∈A:=
      Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩
    rw [hψ _ hx]
    exact hf z ⟨k,by omega⟩
  constructor
  · intro z k hk
    rw [hmap z k (by omega),hmap z (k+1) (by omega)]
    apply hdir
    rw [hlen]
    exact hk
  · intro j
    let z:actualOldPieceIndex data:=.inl j
    have hfirst:ψ (data.C j.val).snd=u z:=by
      have hh:=hmap z 0 (Nat.zero_le _)
      simpa only [z,actualOldPieceWalk,actualOldPieceStart,SimpleGraph.Walk.getVert_zero] using hh
    have hlast:ψ (data.root j.val)=v z:=by
      have hh:=hmap z (actualOldPieceWalk data z).length (le_refl _)
      have hsource:(actualOldPieceWalk data z).getVert (actualOldPieceWalk data z).length=data.root j.val:=by
        exact (data.C j.val).tail.getVert_length
      have htarget:(q z).getVert (actualOldPieceWalk data z).length=v z:=by
        rw [←hlen z]
        exact (q z).getVert_length
      rw [hsource,htarget] at hh
      exact hh
    rw [hfirst,hlast]
    exact hclose j
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_cycle_directed_arcs
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V) (R:V→V→Prop)
    (hpieces:∀z k,k<(actualOldPieceWalk data z).length→
      R (ψ ((actualOldPieceWalk data z).getVert k)) (ψ ((actualOldPieceWalk data z).getVert (k+1))))
    (hclose:∀j:{j // j∈data.t},R (ψ (data.root j.val)) (ψ (data.C j.val).snd)):
    ∀j∈data.t,∀k<(data.C j).length,R (ψ ((data.C j).getVert k)) (ψ ((data.C j).getVert (k+1))):=by
  intro j hj k hk
  let q:{j // j∈data.t}:=⟨j,hj⟩
  by_cases hk0:k=0
  · subst k
    have hsnd:(data.C j).getVert 1=(data.C j).snd:=by
      simpa only [SimpleGraph.Walk.getVert_zero] using (SimpleGraph.Walk.getVert_tail (n:=0) (data.C j)).symm
    simpa only [SimpleGraph.Walk.getVert_zero,hsnd] using hclose q
  · have htail:(data.C j).tail.length+1=(data.C j).length:=(data.C j).length_tail_add_one (data.hcycle j hj).not_nil
    have hh:=hpieces (.inl q) (k-1) (by change k-1<(data.C j).tail.length;omega)
    change R (ψ ((data.C j).tail.getVert (k-1))) (ψ ((data.C j).tail.getVert ((k-1)+1))) at hh
    simp only [SimpleGraph.Walk.getVert_tail] at hh
    have h₁:k-1+1=k:=by omega
    have h₂:k-1+1+1=k+1:=by omega
    simpa only [h₁,h₂] using hh
end Oberwolfach
