module

public import Oberwolfach.ActualBufferedComplementEdgeExact
public import Oberwolfach.BufferedCanonicalArcsExactRemaining

@[expose] public section
/-! For one actual buffered factor the canonical arcs enumerate exactly its
old nonfinal edges and the newly embedded residual edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_buffered_canonical_edge_split
    {X V A B J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (data.c*data.d+5)↪X) (inner:∀a:A,Fin (data.c*data.d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (hdis:∀i j:A,i≠j→Disjoint (Finset.univ.image (ext (.inl i))) (Finset.univ.image (ext (.inl j))))
    (e:∀C:F.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (hstep:∀i (k:Fin (data.c*data.d)),factorCycleOrientation F e (inner i k.castSucc)=inner i k.succ)
    (p:∀i:A,F.Walk (inner i 0) (inner i (Fin.last (data.c*data.d))))
    (hlen:∀i,(p i).length=data.c*data.d) (hpsupp:∀i,(p i).support=List.ofFn (inner i))
    (hfinal:(Finset.univ.biUnion (fun i:A=>(p i).edges.toFinset))=
      (Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset)))
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
  have h1:=buffered_canonical_arcs_exact_remaining F hF e (fun _:A=>data.c*data.d) (fun i=>ext (.inl i)) inner hinner hdis hstep p hlen hpsupp hσ fC
  rw [hfinal] at h1
  have h2:=actual_buffered_complement_edge_exact data hF hCycle hs ext inner hsupp hinner fC ψ Φ hold hnew
  exact h1.trans h2
end Oberwolfach
