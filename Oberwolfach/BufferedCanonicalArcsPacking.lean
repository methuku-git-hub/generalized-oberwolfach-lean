module

public import Oberwolfach.BufferedCanonicalArcsFromRemainingEdges
public import Oberwolfach.DirectedArcsFromPhysicalPacking

@[expose] public section
/-! Packed remaining factor-edge images give disjoint canonical directed arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_canonical_arcs_disjoint_of_remaining_edge_packing
    {U V:Type*} [Fintype U] [DecidableEq V]
    {X I:U→Type*} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)] [∀w,Fintype (I w)]
    (G:∀w,SimpleGraph (X w)) (hG:∀w,(G w).IsRegularOfDegree 2)
    (e:∀w (C:(G w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (n:∀w,I w→ℕ) (ext:∀w i,Fin (n w i+5)↪X w) (inner:∀w i,Fin (n w i+1)↪X w)
    (hinner:∀w i p,inner w i p=ext w i ⟨p.val+2,by omega⟩)
    (hdis:∀w i j,i≠j→Disjoint (Finset.univ.image (ext w i)) (Finset.univ.image (ext w j)))
    (hstep:∀w i (p:Fin (n w i)),factorCycleOrientation (G w) (e w) (inner w i p.castSucc)=inner w i p.succ)
    (p:∀w i,(G w).Walk (inner w i 0) (inner w i (Fin.last (n w i))))
    (hlen:∀w i,(p w i).length=n w i) (hsupp:∀w i,(p w i).support=List.ofFn (inner w i))
    (hσ:∀w,(complementTailDomain (bufferedPathFullDomain (n w) (inner w)) (bufferedFinalEndpoints (n w) (inner w))).image
      (factorCycleOrientation (G w) (e w))=complementTailDomain (bufferedPathFullDomain (n w) (inner w)) (bufferedInitialEndpoints (n w) (inner w)))
    (fC:∀w,{x // x∉bufferedPathStrictInterior (n w) (inner w)}↪V):
    let tail:=fun w=>bufferedOrientedTailEmbedding (n w) (ext w) (inner w) (hinner w) (hdis w) (fC w)
    let head:=fun w=>bufferedOrientedHeadEmbedding (n w) (ext w) (inner w) (hinner w) (hdis w) (factorCycleOrientation (G w) (e w)) (hσ w) (fC w)
    let remaining:=fun w=>(((G w).deleteEdges (↑(Finset.univ.biUnion (fun i=>(p w i).edges.toFinset)):Set (Sym2 (X w)))).induce
      {x | x∉bufferedPathStrictInterior (n w) (inner w)}).edgeFinset.image (Sym2.map (fC w))
    (∀w z,w≠z→Disjoint (remaining w) (remaining z))→
    ∀w z,w≠z→Disjoint (Finset.univ.image (fun x=>(tail w x,head w x)))
      (Finset.univ.image (fun x=>(tail z x,head z x))):=by
  classical
  intro tail head remaining hpack
  apply directed_arcs_disjoint_of_physical_packing (fun w=>Finset.univ.image (fun x=>(tail w x,head w x))) remaining
  · intro w
    rw [Finset.image_image]
    exact buffered_canonical_arcs_in_remaining_edge_image (G w) (hG w) (e w) (n w) (ext w) (inner w)
      (hinner w) (hdis w) (hstep w) (p w) (hlen w) (hsupp w) (hσ w) (fC w)
  · exact hpack
end Oberwolfach
