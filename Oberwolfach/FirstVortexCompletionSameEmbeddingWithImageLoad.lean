module

public import Oberwolfach.FirstVortexResidualCompletionOriented
public import Oberwolfach.PrescribedAssignedCompletionImageLoad
public import Oberwolfach.FirstVortexResidualCompletion
public import Oberwolfach.PrescribedFamilyAvoidPhysicalGraph

@[expose] public section
/-! Expose the prescribed edge family together with the very same residual
and complement embeddings that produced it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance completionSameEmbeddingWithImageLoadFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_completion_same_embedding_with_image_load
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (Dsrc:U→Fin n→Fin n→Prop)
    (K J:U→Type) [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (a:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (Interiors:U→Finset (Fin n)) (ψ:U→Fin n→Fin n)
    (Kbad Jbad Used R:SimpleGraph (Fin n)) (Lbad:Sym2 (Fin n)→Finset U)
    (Bad:Fin n→Finset U) (Z:U→Finset (Fin n))
    (Dfree Dstar:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n)))
    (Lists:U→Finset (Fin n)) (FinalEdges:U→Finset (Sym2 (Fin n))) (δ:ℝ)
    (hPack:Pack⊆Used.edgeFinset) (hUsed:∀x y,Used.Adj x y→¬R.Adj x y)
    (hD:∀x y,Dstar x y→¬R.Adj x y)
    (hglobal:∀v,((Finset.univ.filter (fun i=>v∈(residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1))).card:ℝ)+
      Kbad.degree v+((Finset.univ.filter (fun i=>v∈Z i)).card:ℝ)≤δ*Fintype.card (Fin n)):
    FirstVortexResidualCompletionOriented F Dsrc K J a Interiors ψ Kbad Jbad Lbad Bad Z Dfree
      Dstar Pack Lists FinalEdges δ→
    ∃ (pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}))
      (Φ:∀i,{x // x∈(a i).remaining}→Fin n) (fC:∀i,{x // x∉Interiors i}↪Fin n),
      (∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (Fin n))) ∧
      (∀i (x:{x // x∉Interiors i}),x.val∈(a i).oldDomain→fC i x=ψ i x.val) ∧
      (∀i (x:{x // x∈(a i).remaining}) (hx:x.val∉Interiors i),fC i ⟨x.val,hx⟩=Φ i x) ∧
      (∀i v,v∈Z i→∃x,Φ i x=v) ∧
      (∀v,((Finset.univ.filter (fun i=>v∈Finset.univ.image (Φ i))).card:ℝ)≤
        δ*Fintype.card (Fin n)+(Real.sqrt δ*Fintype.card (Fin n)+1)) ∧
      let E:U→Finset (Sym2 (Fin n)):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
      PairwisePhysicalDisjoint E ∧ Kbad.edgeFinset⊆Finset.univ.biUnion E ∧
      (∀i,Disjoint (E i) Jbad.edgeFinset) ∧ (∀i,Disjoint (E i) Pack) ∧
      (∀i j,i≠j→Disjoint
        (((((F i).deleteEdges (↑(FinalEdges i):Set (Sym2 (Fin n)))).induce {x | x∉Interiors i}).edgeFinset).image (Sym2.map (fC i)))
        (((((F j).deleteEdges (↑(FinalEdges j):Set (Sym2 (Fin n)))).induce {x | x∉Interiors j}).edgeFinset).image (Sym2.map (fC j)))) ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card (Fin n)) ∧
      (∀x y,(SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E).Adj x y→¬R.Adj x y):=by
  intro hcompletion
  rcases hcompletion with ⟨pieces,hgraph,harcs,assign,orient,B,g,Φ,fC,hOrient,hOld,hΦ,hB,hbad,hlist,hΦg,hZ,hLists,hDstar,hpair,hcover,hJ,hPackAvoid,hdis,hload,hunion,hdegree⟩
  let E:=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))
  have hreserve:∀x y,(prescribedPhysicalUnion E).Adj x y→¬R.Adj x y:=by
    apply prescribed_family_avoids_physical_graph pieces Φ Dstar R ?_ hD
    intro i x y h
    exact (hDstar i x y h).1
  have hImage:=prescribed_assigned_completion_image_load Kbad assign orient hOrient Φ B g
    (fun i=>(residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1)) Z
    (fun i=>(hB i).2.2) hΦg (δ*Fintype.card (Fin n)) (Real.sqrt δ*Fintype.card (Fin n)+1) hglobal hload
  refine ⟨pieces,Φ,fC,hgraph,hOld,hΦ,hZ,hImage,hpair,hcover,hJ,hPackAvoid,hdis,hdegree,?_⟩
  intro x y h
  rcases h with h|h
  · exact hUsed x y (SimpleGraph.mem_edgeFinset.mp (hPack ((SimpleGraph.fromEdgeSet_adj _).mp h).1))
  · exact hreserve x y h
end Oberwolfach
