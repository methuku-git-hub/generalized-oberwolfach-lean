module

public import Oberwolfach.ActualMatchedOrdinaryRimsOld
public import Oberwolfach.ActualMatchedPiecePhysicalEdges

@[expose] public section
/-! Retain all ordinary-wheel rim edges in the old packing obtained from the
same matched source and target walks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_ordinary_wheel_edges
    {X V U K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (π:Equiv.Perm V) (b:ℕ) (n:{j // j∈data.t}→ℕ) (hn:∀j,2≤n j)
    (C:∀j:{j // j∈data.t},OrderedOrdinaryWheel (U:=U) π b (n j+1))
    (u v:actualOldPieceIndex data→V) (q:∀z,(SimpleGraph.completeGraph V).Walk (u z) (v z))
    (hq:∀z,(q z).IsPath) (hlen:∀z,(q z).length=(actualOldPieceWalk data z).length)
    (hcycle:∀j:{j // j∈data.t},(data.C j.val).length=n j+1)
    (hends:∀j:{j // j∈data.t},u (.inl j)=(C j).1.val (cycleNext 0) ∧ v (.inl j)=(C j).1.val 0)
    (hcedges:∀j:{j // j∈data.t},∀k,k<(q (.inl j)).length→∃a:Fin (n j+1),
      (q (.inl j)).getVert k=(C j).1.val a ∧ (q (.inl j)).getVert (k+1)=(C j).1.val (cycleNext a))
    (ψ:X→V):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(g:{x // x∈A}↪V),
    (∀x (hx:x∈A),ψ x=g ⟨x,hx⟩)→
    (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      g ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
        (q z).getVert k.val)→
    ∀j (i:Fin (n j+1)),s((C j).1.val i,(C j).1.val (cycleNext i))∈
      (data.deletedEdges\(Finset.univ.biUnion (fun x:{x // x∈data.s₁}=>(data.path (.inl x)).edges.toFinset))).image (Sym2.map ψ):=by
  intro A g hψ hg j i
  let f:Fin (n j+1)↪V:=⟨(C j).1.val,permutationSeparated_injective π b (C j).1.val (C j).1.property⟩
  let q':=(q (.inl j)).copy (hends j).1 (hends j).2
  have hp:q'.IsPath:=by simpa only [q',SimpleGraph.Walk.isPath_copy] using hq (.inl j)
  have hlenSource:q'.length=(data.C j.val).tail.length:=by
    simpa only [q',SimpleGraph.Walk.length_copy,actualOldPieceWalk] using hlen (.inl j)
  have hlenQ:q'.length=n j:=by
    rw [hlenSource,SimpleGraph.Walk.length_tail,hcycle]
    omega
  have hcover:∀edge∈q'.edges,∃a:Fin (n j+1),edge=s(f a,f (cycleNext a)):=by
    intro edge he
    have he':edge∈(q (.inl j)).edges:=by simpa only [q',SimpleGraph.Walk.edges_copy] using he
    induction edge using Sym2.ind with
    | _ x y =>
      obtain ⟨k,hk,heq⟩:=((q (.inl j)).mk_mem_edges_iff_exists).mp he'
      obtain ⟨a,ha,hb⟩:=hcedges j k hk
      refine ⟨a,?_⟩
      change s(x,y)=s((C j).1.val a,(C j).1.val (cycleNext a))
      simpa only [ha,hb] using heq.symm
  have hmap:∀k,k≤(data.C j.val).tail.length→ψ ((data.C j.val).tail.getVert k)=q'.getVert k:=by
    intro k hk
    have hx:(actualOldPieceWalk data (.inl j)).getVert k∈A:=
      Finset.mem_biUnion.mpr ⟨.inl j,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data (.inl j)).getVert_mem_support _)⟩
    have hh:=hg (.inl j) ⟨k,by simpa only [actualOldPieceWalk] using Nat.lt_succ_of_le hk⟩
    rw [←hψ _ hx] at hh
    simpa only [actualOldPieceWalk,q',SimpleGraph.Walk.getVert_copy] using hh
  have hfirst:ψ ((data.C j.val).snd)=f (cycleNext 0):=by
    have h:=hmap 0 (Nat.zero_le _)
    change ψ ((data.C j.val).snd)=(C j).1.val (cycleNext 0)
    simpa only [SimpleGraph.Walk.getVert_zero,actualOldPieceWalk,q',SimpleGraph.Walk.getVert_copy,hends] using h
  have hlast:ψ (data.root j.val)=f 0:=by
    have h:=hmap (data.C j.val).tail.length (le_refl _)
    rw [SimpleGraph.Walk.getVert_length,←hlenSource,SimpleGraph.Walk.getVert_length] at h
    exact h
  exact actual_matched_ordinary_rims_old data j (n j) (hn j) f (SimpleGraph.completeGraph V) q' hp hlenQ hcover ψ hlenSource hmap hfirst hlast i
end Oberwolfach
