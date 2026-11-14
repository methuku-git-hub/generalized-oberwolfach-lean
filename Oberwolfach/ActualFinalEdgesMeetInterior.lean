module

public import Oberwolfach.BufferedFinalEdgesMeetInterior
public import Oberwolfach.ActualSumBufferedInteriorsDeleted

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_final_edges_meet_buffered_interior
    {X A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F)
    (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (data.c*data.d+5)↪X)
    (inner:∀a:A,Fin (data.c*data.d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩):
    ∀e∈Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset),
      ∃x∈e.toFinset,x∈bufferedPathStrictInterior (fun _:A=>data.c*data.d) inner :=by
  let ix (a:A):{i // i∈data.s₁}:=⟨.inl a,by rw [hs];simp [firstSumIndices]⟩
  have hpath:∀a,(data.path (.inl (ix a))).support=List.ofFn (inner a):=by
    intro a
    exact (actual_final_path_matches_buffered_sequence data (ix a) (ext (.inl a)) (inner a) (hinner a) (hsupp (.inl a))).2.2
  have hsize:2≤data.c*data.d:=by nlinarith [data.hc,data.hd]
  have hAll:=buffered_final_edges_meet_strict_interior F (fun _:A=>data.c*data.d) inner
    (fun a=>data.start (.inl (ix a))) (fun a=>data.finish (.inl (ix a)))
    (fun a=>data.path (.inl (ix a))) (fun _=>hsize) hpath
  intro e he
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
  cases hval:i.val with
  | inl a =>
    have hii:i=ix a:=Subtype.ext hval
    subst i
    exact hAll e (Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,hi⟩)
  | inr b =>
    have hh:i.val∈firstSumIndices:=by rw [←hs];exact i.property
    rw [hval] at hh
    simp [firstSumIndices] at hh
theorem actual_final_edges_meet_buffered_interior_with_parameters
    {X A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F)
    (c d:ℕ) (hc:data.c=c) (hd:data.d=d) (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (c*d+5)↪X) (inner:∀a:A,Fin (c*d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩):
    ∀e∈Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset),
      ∃x∈e.toFinset,x∈bufferedPathStrictInterior (fun _:A=>c*d) inner :=by
  subst c
  subst d
  exact actual_final_edges_meet_buffered_interior data hs ext inner hsupp hinner

end Oberwolfach
