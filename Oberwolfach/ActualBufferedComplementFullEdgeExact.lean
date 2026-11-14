module

public import Oberwolfach.ActualBufferedComplementEdgeExact
public import Oberwolfach.InducedComplementDeleteInterior

@[expose] public section
/-! On the complement of the strict path interiors, the original factor has
exactly the old nonfinal and completed residual edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_buffered_complement_full_edge_exact
    {X V A B J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (c d:ℕ) (hc:data.c=c) (hd:data.d=d) (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (c*d+5)↪X) (inner:∀a:A,Fin (c*d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩):
    let Interiors:=bufferedPathStrictInterior (fun _:A=>c*d) inner
    let Final:=Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset);
    ∀(fC:{x // x∉Interiors}↪V) (ψ:X→V) (Φ:{x // x∈data.remaining}→V),
    (∀(x:{x // x∉Interiors}),x.val∈data.oldDomain→fC x=ψ x.val)→
    (∀(x:{x // x∉Interiors}) (hx:x.val∈data.remaining),fC x=Φ ⟨x.val,hx⟩)→
    ((F.induce {x | x∉Interiors}).edgeFinset).image (Sym2.map fC)=
      (data.deletedEdges\Final).image (Sym2.map ψ) ∪
        ((data.graph.induce (↑data.remaining:Set X)).edgeFinset).image (Sym2.map Φ):=by
  subst c
  subst d
  intro Interiors Final fC ψ Φ hold hnew
  have hmeet:∀e∈Final,∃x∈e.toFinset,x∈Interiors:=
    actual_final_edges_meet_buffered_interior data hs ext inner hsupp hinner
  have hgraph:(F.deleteEdges (↑Final:Set (Sym2 X))).induce {x | x∉Interiors}=F.induce {x | x∉Interiors}:=
    induce_complement_delete_edges_meeting_set F Interiors Final hmeet
  have hh:=actual_buffered_complement_edge_exact data hF hCycle hs ext inner hsupp hinner fC ψ Φ hold hnew
  have heq:(((F.deleteEdges (↑Final:Set (Sym2 X))).induce {x | x∉Interiors}).edgeFinset)=
      (F.induce {x | x∉Interiors}).edgeFinset:=by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [hgraph]
  rw [heq] at hh
  exact hh
end Oberwolfach
