module

public import Oberwolfach.ActualCanonicalArcHostContainment
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

theorem actual_canonical_arcs_in_host_from_residual_digraph
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
    (Dsmall:{x // x∈data.remaining}→{x // x∈data.remaining}→Prop)
    (hmodel:∀x y,Dsmall x y↔Dsrc x.val y.val ∧ data.graph.Adj x.val y.val)
    (Dtarget:V→V→Prop) (hembed:∀x y,Dsmall x y→Dtarget (Φ x) (Φ y))
    (hhost:∀x y,Dtarget x y→(x,y)∈H):
    let tail:=bufferedOrientedTailEmbedding n ext inner hinner hdis fC
    let head:=bufferedOrientedHeadEmbedding n ext inner hinner hdis (factorCycleOrientation G e) hσ fC
    Finset.univ.image (fun z=>(tail z,head z))⊆H:=by
  have hNewArc:∀(x y:{x // x∈data.remaining}),Dsrc x.val y.val→data.graph.Adj x.val y.val→(Φ x,Φ y)∈H:=by
    intro x y hxy hadj
    exact hhost (Φ x) (Φ y) (hembed x y ((hmodel x y).2 ⟨hxy,hadj⟩))
  exact actual_canonical_arcs_in_host_from_old_and_new G hG e n ext inner hinner hdis hstep p hlen hsupp hσ
    data hCycle fC ψ Φ hold hnew Dsrc horient H hOldArc hNewArc
end Oberwolfach
