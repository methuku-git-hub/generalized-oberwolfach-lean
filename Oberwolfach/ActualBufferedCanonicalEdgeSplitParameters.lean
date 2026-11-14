module

public import Oberwolfach.ActualBufferedCanonicalEdgeSplitConcrete

@[expose] public section
/-! The actual final paths themselves provide the walk family in the exact
canonical edge split; no independently chosen family is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_buffered_canonical_edge_split_with_parameters
    {X V A B J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (c d:ℕ) (hc:data.c=c) (hd:data.d=d) (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (c*d+5)↪X) (inner:∀a:A,Fin (c*d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (hdis:∀i j:A,i≠j→Disjoint (Finset.univ.image (ext (.inl i))) (Finset.univ.image (ext (.inl j))))
    (e:∀C:F.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (hextstep:∀i (k:Fin (c*d+4)),factorCycleOrientation F e (ext (.inl i) k.castSucc)=ext (.inl i) k.succ)
    (hσ:(complementTailDomain (bufferedPathFullDomain (fun _:A=>c*d) inner)
      (bufferedFinalEndpoints (fun _:A=>c*d) inner)).image (factorCycleOrientation F e)=
      complementTailDomain (bufferedPathFullDomain (fun _:A=>c*d) inner)
        (bufferedInitialEndpoints (fun _:A=>c*d) inner))
    (fC:{x // x∉bufferedPathStrictInterior (fun _:A=>c*d) inner}↪V)
    (ψ:X→V) (Φ:{x // x∈data.remaining}→V)
    (hold:∀x:{x // x∉bufferedPathStrictInterior (fun _:A=>c*d) inner},x.val∈data.oldDomain→fC x=ψ x.val)
    (hnew:∀(x:{x // x∉bufferedPathStrictInterior (fun _:A=>c*d) inner}) (hx:x.val∈data.remaining),fC x=Φ ⟨x.val,hx⟩):
    let tail:=bufferedOrientedTailEmbedding (fun _:A=>c*d) (fun i=>ext (.inl i)) inner hinner hdis fC
    let head:=bufferedOrientedHeadEmbedding (fun _:A=>c*d) (fun i=>ext (.inl i)) inner hinner hdis (factorCycleOrientation F e) hσ fC
    (Finset.univ.image (fun z=>s(tail z,head z)))=
      (data.deletedEdges\(Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ) ∪
      ((data.graph.induce (↑data.remaining:Set X)).edgeFinset).image (Sym2.map Φ):=by
  subst c
  subst d
  exact actual_buffered_canonical_edge_split_concrete data hF hCycle hs ext inner hsupp hinner hdis e hextstep hσ fC ψ Φ hold hnew
end Oberwolfach
