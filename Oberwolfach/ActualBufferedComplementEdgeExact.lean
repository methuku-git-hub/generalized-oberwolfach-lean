module

public import Oberwolfach.ActualBufferedFinalEdgeIncidence
public import Oberwolfach.ActualRestrictedEdgeImageExact

@[expose] public section
/-! The actual old nonfinal edges and the prescribed residual edges are
exactly the edges of the complement embedding of the buffered paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_buffered_complement_edge_exact
    {X V A B J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (data.c*data.d+5)↪X)
    (inner:∀a:A,Fin (data.c*data.d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩):
    let Interiors:=bufferedPathStrictInterior (fun _:A=>data.c*data.d) inner
    let Final:=Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset);
    ∀(fC:{x // x∉Interiors}↪V) (ψ:X→V) (Φ:{x // x∈data.remaining}→V),
    (∀(x:{x // x∉Interiors}),x.val∈data.oldDomain→fC x=ψ x.val)→
    (∀(x:{x // x∉Interiors}) (hx:x.val∈data.remaining),fC x=Φ ⟨x.val,hx⟩)→
    (((F.deleteEdges (↑Final:Set (Sym2 X))).induce {x | x∉Interiors}).edgeFinset).image (Sym2.map fC)=
      (data.deletedEdges\Final).image (Sym2.map ψ) ∪
        ((data.graph.induce (↑data.remaining:Set X)).edgeFinset).image (Sym2.map Φ):=by
  intro Interiors Final fC ψ Φ hold hnew
  have hinc:=actual_buffered_final_edge_incidence data hF hs ext inner hsupp hinner
  have hdis:=actual_sum_buffered_interiors_deleted data hs ext inner hsupp hinner
  apply actual_restricted_edge_image_exact F hF data hCycle Interiors Final fC ψ Φ hold hnew hinc.2.2 ?_ hinc.2.1
  intro x hx hI
  exact Finset.disjoint_left.mp hdis hI hx
end Oberwolfach
