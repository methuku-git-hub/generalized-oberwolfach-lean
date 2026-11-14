module

public import Oberwolfach.ActualBufferedCanonicalEdgeSplit

@[expose] public section
/-! The actual final paths themselves provide the walk family in the exact
canonical edge split; no independently chosen family is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_buffered_canonical_edge_split_concrete
    {X V A B J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (data.c*data.d+5)↪X) (inner:∀a:A,Fin (data.c*data.d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (hdis:∀i j:A,i≠j→Disjoint (Finset.univ.image (ext (.inl i))) (Finset.univ.image (ext (.inl j))))
    (e:∀C:F.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (hextstep:∀i (k:Fin (data.c*data.d+4)),factorCycleOrientation F e (ext (.inl i) k.castSucc)=ext (.inl i) k.succ)
    (hσ:(complementTailDomain (bufferedPathFullDomain (fun _:A=>data.c*data.d) inner)
      (bufferedFinalEndpoints (fun _:A=>data.c*data.d) inner)).image (factorCycleOrientation F e)=
      complementTailDomain (bufferedPathFullDomain (fun _:A=>data.c*data.d) inner)
        (bufferedInitialEndpoints (fun _:A=>data.c*data.d) inner))
    (fC:{x // x∉bufferedPathStrictInterior (fun _:A=>data.c*data.d) inner}↪V)
    (ψ:X→V) (Φ:{x // x∈data.remaining}→V)
    (hold:∀x:{x // x∉bufferedPathStrictInterior (fun _:A=>data.c*data.d) inner},x.val∈data.oldDomain→fC x=ψ x.val)
    (hnew:∀(x:{x // x∉bufferedPathStrictInterior (fun _:A=>data.c*data.d) inner}) (hx:x.val∈data.remaining),fC x=Φ ⟨x.val,hx⟩):
    let tail:=bufferedOrientedTailEmbedding (fun _:A=>data.c*data.d) (fun i=>ext (.inl i)) inner hinner hdis fC
    let head:=bufferedOrientedHeadEmbedding (fun _:A=>data.c*data.d) (fun i=>ext (.inl i)) inner hinner hdis (factorCycleOrientation F e) hσ fC
    (Finset.univ.image (fun z=>s(tail z,head z)))=
      (data.deletedEdges\(Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ) ∪
      ((data.graph.induce (↑data.remaining:Set X)).edgeFinset).image (Sym2.map Φ):=by
  intro tail head
  let ix (a:A):{i // i∈data.s₁}:=⟨.inl a,by rw [hs];simp [firstSumIndices]⟩
  have hp:∀a,data.start (.inl (ix a))=inner a 0 ∧
      data.finish (.inl (ix a))=inner a (Fin.last (data.c*data.d)) ∧
      (data.path (.inl (ix a))).support=List.ofFn (inner a):=by
    intro a
    exact actual_final_path_matches_buffered_sequence data (ix a) (ext (.inl a)) (inner a) (hinner a) (hsupp (.inl a))
  let p:=fun a:A=>(data.path (.inl (ix a))).copy (hp a).1 (hp a).2.1
  have hpsupp:∀a,(p a).support=List.ofFn (inner a):=by
    intro a
    simpa only [p,SimpleGraph.Walk.support_copy] using (hp a).2.2
  have hlen:∀a,(p a).length=data.c*data.d:=by
    intro a
    have h:=congrArg List.length (hpsupp a)
    simp only [SimpleGraph.Walk.length_support,List.length_ofFn] at h
    omega
  have hfinal:(Finset.univ.biUnion (fun i:A=>(p i).edges.toFinset))=
      (Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset)):=by
    ext edge
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,ha⟩
      refine ⟨ix a,?_⟩
      simpa only [p,SimpleGraph.Walk.edges_copy] using ha
    · rintro ⟨i,hi⟩
      cases hv:i.val with
      | inl a =>
        have hie:i=ix a:=Subtype.ext hv
        subst i
        refine ⟨a,?_⟩
        simpa only [p,SimpleGraph.Walk.edges_copy] using hi
      | inr b =>
        have hh:i.val∈firstSumIndices:=by rw [←hs];exact i.property
        rw [hv] at hh
        simp [firstSumIndices] at hh
  have hstep:∀i (k:Fin (data.c*data.d)),factorCycleOrientation F e (inner i k.castSucc)=inner i k.succ:=by
    intro i k
    rw [hinner i k.castSucc,hinner i k.succ]
    have h:=hextstep i ⟨k.val+2,by omega⟩
    convert h using 1 <;> congr! 3 <;> apply Fin.ext <;> simp
  exact actual_buffered_canonical_edge_split data hF hCycle hs ext inner hsupp hinner hdis e hstep p hlen hpsupp hfinal hσ fC ψ Φ hold hnew
end Oberwolfach
