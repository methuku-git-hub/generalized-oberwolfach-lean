module

public import Oberwolfach.BufferedFactorRemainingEdges
public import Oberwolfach.BufferedCanonicalOrientedArcs
public import Oberwolfach.ResidualActualPhysicalEdges

@[expose] public section
/-! Directed host containment of canonical complement arcs from the actual
old and residual directed embeddings, with one compatible source orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_canonical_arcs_in_host_from_old_and_new
    {X V I K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I] [DecidableEq K] [DecidableEq J]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (hstep:∀i (p:Fin (n i)),factorCycleOrientation G e (inner i p.castSucc)=inner i p.succ)
    (p:∀i,G.Walk (inner i 0) (inner i (Fin.last (n i))))
    (hlen:∀i,(p i).length=n i) (hsupp:∀i,(p i).support=List.ofFn (inner i))
    (hσ:(complementTailDomain (bufferedPathFullDomain n inner) (bufferedFinalEndpoints n inner)).image
      (factorCycleOrientation G e)=complementTailDomain (bufferedPathFullDomain n inner) (bufferedInitialEndpoints n inner))
    (data:ActualResidualData (K:=K) (J:=J) G) (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V) (ψ:X→V) (Φ:{x // x∈data.remaining}→V)
    (hold:∀(x:{x // x∉bufferedPathStrictInterior n inner}),x.val∈data.oldDomain→fC x=ψ x.val)
    (hnew:∀(x:{x // x∉bufferedPathStrictInterior n inner}) (hx:x.val∈data.remaining),fC x=Φ ⟨x.val,hx⟩)
    (Dsrc:X→X→Prop) (horient:∀x,Dsrc x (factorCycleOrientation G e x)) (H:Finset (V×V))
    (hOldArc:∀x y,s(x,y)∈data.deletedEdges\(Finset.univ.biUnion (fun i=>(p i).edges.toFinset))→
      Dsrc x y→(ψ x,ψ y)∈H)
    (hNewArc:∀(x y:{x // x∈data.remaining}),Dsrc x.val y.val→data.graph.Adj x.val y.val→(Φ x,Φ y)∈H):
    let tail:=bufferedOrientedTailEmbedding n ext inner hinner hdis fC
    let head:=bufferedOrientedHeadEmbedding n ext inner hinner hdis (factorCycleOrientation G e) hσ fC
    Finset.univ.image (fun z=>(tail z,head z))⊆H:=by
  classical
  intro tail head
  let A:=bufferedPathFullDomain n inner
  let D:=bufferedPathStrictInterior n inner
  let B:=bufferedFinalEndpoints n inner
  let T:=bufferedInitialEndpoints n inner
  let σ:=factorCycleOrientation G e
  let E:=Finset.univ.biUnion (fun i=>(p i).edges.toFinset)
  have hDA:D⊆A:=buffered_strict_interior_subset_domain n inner
  have hBD:Disjoint B D:=buffered_final_endpoints_disjoint_strict n ext inner hinner hdis
  have hTD:Disjoint T D:=buffered_initial_endpoints_disjoint_strict n ext inner hinner hdis
  intro z hz
  obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hz
  have hx:x.val∉D:=by
    intro hd
    rcases Finset.mem_union.mp x.property with hout | hb
    · exact (Finset.mem_sdiff.mp hout).2 (hDA hd)
    · exact Finset.disjoint_left.mp hBD hb hd
  have hy:σ x.val∉D:=by
    have hh:σ x.val∈complementTailDomain A T:=by
      rw [←hσ]
      exact Finset.mem_image.mpr ⟨x.val,x.property,rfl⟩
    intro hd
    rcases Finset.mem_union.mp hh with hout | ht
    · exact (Finset.mem_sdiff.mp hout).2 (hDA hd)
    · exact Finset.disjoint_left.mp hTD ht hd
  let a:{x // x∉D}:=⟨x.val,hx⟩
  let b:{x // x∉D}:=⟨σ x.val,hy⟩
  have hsource:s(x.val,σ x.val)∈G.edgeFinset\E:=by
    rw [buffered_factor_remaining_edges G hG e n ext inner hinner hdis hstep p hlen hsupp]
    exact Finset.mem_image.mpr ⟨x.val,x.property,rfl⟩
  change (fC a,fC b)∈H
  by_cases hd:s(x.val,σ x.val)∈data.deletedEdges
  · have hxo:x.val∈data.oldDomain:=data.deleted_edge_vertices_in_old_domain hCycle _ hd x.val (by simp)
    have hyo:σ x.val∈data.oldDomain:=data.deleted_edge_vertices_in_old_domain hCycle _ hd (σ x.val) (by simp)
    rw [hold a hxo,hold b hyo]
    exact hOldArc x.val (σ x.val) (Finset.mem_sdiff.mpr ⟨hd,(Finset.mem_sdiff.mp hsource).2⟩) (horient x.val)
  · have hgraph:data.graph.Adj x.val (σ x.val):=by
      change s(x.val,σ x.val)∈data.graph.edgeSet
      apply SimpleGraph.mem_edgeFinset.mp
      rw [SimpleGraph.edgeFinset_deleteEdges]
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hsource).1,hd⟩
    have hnograph:∀z,z∉data.remaining→∀w,¬data.graph.Adj z w:=(data.graph_facts hG).2.2.2.2.1
    have hxr:x.val∈data.remaining:=by by_contra h;exact hnograph _ h _ hgraph
    have hyr:σ x.val∈data.remaining:=by by_contra h;exact hnograph _ h _ hgraph.symm
    rw [hnew a hxr,hnew b hyr]
    exact hNewArc ⟨x.val,hxr⟩ ⟨σ x.val,hyr⟩ (horient x.val) hgraph
end Oberwolfach
