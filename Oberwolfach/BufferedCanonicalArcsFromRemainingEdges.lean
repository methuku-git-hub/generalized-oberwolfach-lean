module

public import Oberwolfach.BufferedFactorRemainingEdges
public import Oberwolfach.BufferedCanonicalOrientedArcs

@[expose] public section
/-! Each canonical mapped oriented arc is an edge of the actual complement
factor mapped by the same complement embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_canonical_arcs_in_remaining_edge_image
    {X V I:Type*} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]
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
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V):
    let tail:=bufferedOrientedTailEmbedding n ext inner hinner hdis fC
    let head:=bufferedOrientedHeadEmbedding n ext inner hinner hdis (factorCycleOrientation G e) hσ fC
    let R:=G.deleteEdges (↑(Finset.univ.biUnion (fun i=>(p i).edges.toFinset)):Set (Sym2 X))
    (Finset.univ.image (fun z=>s(tail z,head z)))⊆
      ((R.induce {x | x∉bufferedPathStrictInterior n inner}).edgeFinset).image (Sym2.map fC):=by
  classical
  intro tail head R
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
  have hR:R.Adj x.val (σ x.val):=by
    change s(x.val,σ x.val) ∈ R.edgeSet
    apply SimpleGraph.mem_edgeFinset.mp
    rw [SimpleGraph.edgeFinset_deleteEdges]
    exact hsource
  refine Finset.mem_image.mpr ⟨s(a,b),?_,?_⟩
  · apply SimpleGraph.mem_edgeFinset.mpr
    exact hR
  · change s(fC a,fC b)=s(tail x,head x)
    rfl
end Oberwolfach
