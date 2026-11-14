module

public import Oberwolfach.FirstVortexResidualCompletionOrientedRestricted
public import Oberwolfach.FirstVortexResidualCompletionOrientedTracked
public import Oberwolfach.PrescribedAssignedCompletionImageLoad
public import Oberwolfach.PrescribedFamilyAvoidPhysicalGraph
public import Oberwolfach.ActualRestrictedDirectedHost
public import Oberwolfach.ActualResidualAnchorRootAvoidance
public import Oberwolfach.FirstVortexResidualCompletion
public import Oberwolfach.ActualRestrictedEdgeHost
public import Oberwolfach.InducedComplementDeleteInterior

@[expose] public section
/-! The completed residual maps embed the entire complement of the reserved
path interiors, and those complement images are pairwise edge-disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance actualResidualSameDirectedImageRestrictedFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem actual_residual_completion_same_directed_complement_with_restricted_image_load
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (A B J:U→Type) [∀w,Fintype (A w)] [∀w,DecidableEq (A w)] [∀w,DecidableEq (B w)] [∀w,DecidableEq (J w)]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2) (H:SimpleGraph (Fin n))
    (Dsrc:U→Fin n→Fin n→Prop) (data:∀w,ActualResidualData (K:=A w⊕B w) (J:=J w) (F w))
    (c d:ℕ) (hc:∀w,(data w).c=c) (hd:∀w,(data w).d=d)
    (hs:∀w,(data w).s₁=firstSumIndices)
    (ext:∀w (i:A w⊕B w),Fin (c*d+5)↪Fin n)
    (inner:∀w (a:A w),Fin (c*d+1)↪Fin n)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hinner:∀w a k,inner w a k=ext w (.inl a) ⟨k.val+2,by omega⟩)
    (hCycle:∀w,(data w).t.biUnion (fun j=>((data w).C j).support.toFinset)⊆(data w).Cembed)
    (ψ:U→Fin n→Fin n) (Kbad Jbad:SimpleGraph (Fin n)) (Lbad:Sym2 (Fin n)→Finset U)
    (Bad:Fin n→Finset U) (Z:U→Finset (Fin n)) (Dfree Dstar:Fin n→Fin n→Prop)
    (Pack:Finset (Sym2 (Fin n))) (Lists:U→Finset (Fin n)) (δ α:ℝ)
    (Htrack:Finset U) (aScale κ:ℝ)
    (hOld:∀w,(((data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w)))⊆Pack)
    (hPack:Pack⊆H.edgeFinset)
    (hOrient:∀w x y,(F w).Adj x y→Dsrc w x y ∨ Dsrc w y x)
    (hDstar:∀x y,Dstar x y→H.Adj x y)
    (hOldArc:∀w x y,s(x,y)∈(data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))→Dsrc w x y→Dstar (ψ w x) (ψ w y))
    (Y:U→Finset (Fin n))
    (hYBad:∀w v,v∈Y w→w∈Bad v) (hZY:∀w,Disjoint (Z w) (Y w))
    (hLY:∀w,Disjoint (Lists w) (Y w))
    (Used Reserve:SimpleGraph (Fin n))
    (hPackUsed:Pack⊆Used.edgeFinset) (hUsedReserve:∀x y,Used.Adj x y→¬Reserve.Adj x y)
    (hDReserve:∀x y,Dstar x y→¬Reserve.Adj x y)
    (hOldAvoid:∀w x,x∈(data w).oldDomain→x∉bufferedPathFullDomain (fun _:A w=>c*d) (inner w)→ψ w x∉Y w)
    (hglobal:∀v,((Finset.univ.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*Fintype.card (Fin n)):
    let Interiors:=fun w=>bufferedPathStrictInterior (fun _:A w=>c*d) (inner w)
    let FinalEdges:=fun w=>Finset.univ.biUnion (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset)
    FirstVortexResidualCompletionOrientedRestricted F Dsrc (fun w=>A w⊕B w) J data Interiors ψ Kbad Jbad Lbad Bad Z Dfree Dstar Pack Lists FinalEdges δ α Htrack aScale κ →
    ∃(pieces:∀w,List (PrescribedSourcePiece {x // x∈(data w).remaining}))
      (Φ:∀w,{x // x∈(data w).remaining}→Fin n) (fC:∀w,{x // x∉Interiors w}↪Fin n)
      (assign:Sym2 (Fin n)→U) (orient:Sym2 (Fin n)→Fin n×Fin n)
      (BB:∀w,Finset {x // x∈(data w).remaining}) (g:∀w,{x // x∈(data w).remaining}→Fin n),
      (∀w,(prescribedAssignedArcs Kbad assign orient w).card≤⌈4*(Kbad.edgeFinset.card:ℝ)/(α*Fintype.card (Fin n))⌉₊) ∧
      (∀w,prescribedDependentGraph pieces w=((data w).graph).induce (↑(data w).remaining:Set (Fin n))) ∧
      (∀w (x:{x // x∉Interiors w}),x.val∈(data w).oldDomain→fC w x=ψ w x.val) ∧
      (∀w (x:{x // x∈(data w).remaining}) (hx:x.val∉Interiors w),fC w ⟨x.val,hx⟩=Φ w x) ∧
      (∀w v,v∈Z w→∃x,Φ w x=v) ∧
      (∀v,((Finset.univ.filter (fun w=>v∈Finset.univ.image (Φ w))).card:ℝ)≤
        δ*Fintype.card (Fin n)+(Real.sqrt δ*Fintype.card (Fin n)+1)) ∧
      (∀w,Disjoint (outsideBufferedPathImage (fun _:A w=>c*d) (inner w) (fC w)) (Y w)) ∧
      (∀w x y,(F w).Adj x.1 y.1→Dsrc w x.1 y.1→Dstar (fC w x) (fC w y)) ∧
      (∀w x y,(F w).Adj x.1 y.1→H.Adj (fC w x) (fC w y)) ∧
      (∀w z,w≠z→Disjoint
        (((F w).induce {x | x∉Interiors w}).edgeFinset.image (Sym2.map (fC w)))
        (((F z).induce {x | x∉Interiors z}).edgeFinset.image (Sym2.map (fC z)))) ∧
      let E:U→Finset (Sym2 (Fin n)):=fun w=>((prescribedDependentGraph pieces w).edgeFinset).image (Sym2.map (Φ w));
      Kbad.edgeFinset⊆Finset.univ.biUnion E ∧
      (∀w,Disjoint (E w) Jbad.edgeFinset) ∧ (∀w,Disjoint (E w) Pack) ∧
      (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card (Fin n)) ∧
      (∀x y,(SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E).Adj x y→¬Reserve.Adj x y) ∧
      (∀w,(BB w).image (g w)=(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1)∪
        prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient w)∪Z w) ∧
      (∀w v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient w)→
        ∃e∈Kbad.edgeFinset,v∈e.toFinset ∧ w∈Lbad e) ∧
      (∀w x,x∈BB w→Φ w x=g w x) ∧
      (∀w x,x∉BB w→Φ w x∈Lists w) ∧
      (∀e∈Kbad.edgeFinset,prescribedArcPhysical (orient e)=e) ∧
      (∀v,((((Finset.univ.filter (fun z:(Σw,{x // x∈(data w).remaining})=>z.2∉BB z.1)).filter (fun z=>z.1∈Htrack)).filter
        (fun z=>Φ z.1 z.2=v)).card:ℝ)≤κ*aScale+1):=by
  intro Interiors FinalEdges hcompletion
  obtain ⟨pieces,hgraph,harcs,assign,orient,BB,g,Φ,fC,hEdgeOrient,hMcap,hC,hR,hBg,hEnd,hEndList,hΦold,hZ,hL,hArc,hPair,hKcover,hJavoid,hPackAvoid,hPacked,hFree,hUnion,hDegree,hRestricted⟩:=hcompletion
  have hImage:=prescribed_assigned_completion_image_load Kbad assign orient hEdgeOrient Φ BB g
    (fun w=>(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1)) Z
    (fun w=>(hBg w).2.2) hΦold (δ*Fintype.card (Fin n)) (Real.sqrt δ*Fintype.card (Fin n)+1) hglobal hFree
  have hmeet:∀w,∀e∈FinalEdges w,∃x∈e.toFinset,x∈Interiors w:=by
    intro w
    exact actual_final_edges_meet_buffered_interior_with_parameters (data w) c d (hc w) (hd w) (hs w) (ext w) (inner w) (hsupp w) (hinner w)
  have heq:∀w,((F w).deleteEdges (↑(FinalEdges w):Set (Sym2 (Fin n)))).induce {x | x∉Interiors w}=
      (F w).induce {x | x∉Interiors w}:=by
    intro w
    exact induce_complement_delete_edges_meeting_set (F w) (Interiors w) (FinalEdges w) (hmeet w)
  have heqE:∀w,(((F w).deleteEdges (↑(FinalEdges w):Set (Sym2 (Fin n)))).induce {x | x∉Interiors w}).edgeFinset=
      ((F w).induce {x | x∉Interiors w}).edgeFinset:=by
    intro w
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [heq w]
  refine ⟨pieces,Φ,fC,assign,orient,BB,g,hMcap,hgraph,hC,hR,hZ,hImage,?_,?_,?_,?_,hKcover,hJavoid,hPackAvoid,hUnion,hDegree,?_,?_,hEndList,hΦold,hL,hEdgeOrient,hRestricted⟩
  · intro w
    have hDR:=actual_sum_buffered_interiors_deleted_with_parameters (data w) c d (hc w) (hd w) (hs w) (ext w) (inner w) (hsupp w) (hinner w)
    have hEAvoid:Disjoint (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient w)) (Y w):=by
      apply Finset.disjoint_left.mpr
      intro v hv hY
      exact hEnd w v hv (hYBad w v hY)
    exact actual_residual_anchor_root_avoidance (F w) (hF w) (data w) (hCycle w)
      (fun _:A w=>c*d) (inner w) hDR (fC w) (ψ w) (Φ w) (g w) (BB w) (Lists w) (Y w)
      (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient w)) (Z w)
      (hC w) (by intro x hx;exact hR w ⟨x.val,hx⟩ x.property) (hΦold w) (hL w)
      (hBg w).2.2 hEAvoid (hZY w) (hLY w) (hOldAvoid w)
  · intro w
    have hNewDir:∀x y:{x // x∈(data w).remaining},Dsrc w x.1 y.1→(data w).graph.Adj x.1 y.1→Dstar (Φ w x) (Φ w y):=by
      intro x y hx hy
      exact (hArc w x y ((harcs w x y).mpr ⟨hx,hy⟩)).1
    exact actual_restricted_directed_arcs_in_host (F w) (hF w) (data w) (hCycle w) (Interiors w) (FinalEdges w)
      (hmeet w) (fC w) (ψ w) (Φ w) (hC w) (by intro x hx;exact hR w ⟨x.val,hx⟩ x.property)
      (Dsrc w) Dstar (hOldArc w) hNewDir
  · intro w x y hxy
    have hNewArc:∀x y:{x // x∈(data w).remaining},Dsrc w x.1 y.1→(data w).graph.Adj x.1 y.1→H.Adj (Φ w x) (Φ w y):=by
      intro x y hx hy
      apply hDstar
      exact (hArc w x y ((harcs w x y).mpr ⟨hx,hy⟩)).1
    have hhost:=actual_restricted_edge_image_in_host (F w) (hF w) H (data w) (hCycle w)
      (Interiors w) (FinalEdges w) (fC w) (ψ w) (Φ w) (hC w)
      (by intro x hx;exact hR w ⟨x.val,hx⟩ x.property) Pack (hOld w) hPack (Dsrc w) (hOrient w) hNewArc
    have hm:s(x,y)∈((F w).induce {x | x∉Interiors w}).edgeFinset:=SimpleGraph.mem_edgeFinset.mpr hxy
    rw [←heqE w] at hm
    have hh:=hhost (Finset.mem_image.mpr ⟨s(x,y),hm,rfl⟩)
    exact SimpleGraph.mem_edgeFinset.mp hh
  · intro w z hwz
    have hh:=hPacked w z hwz
    rw [heqE w,heqE z] at hh
    exact hh
  · intro x y h
    rcases h with h|h
    · exact hUsedReserve x y (SimpleGraph.mem_edgeFinset.mp (hPackUsed ((SimpleGraph.fromEdgeSet_adj _).mp h).1))
    · have hreserve:∀x y,(prescribedPhysicalUnion (fun w=>((prescribedDependentGraph pieces w).edgeFinset).image (Sym2.map (Φ w)))).Adj x y→¬Reserve.Adj x y:=by
        apply prescribed_family_avoids_physical_graph pieces Φ Dstar Reserve ?_ hDReserve
        intro w u v hv
        exact (hArc w u v hv).1
      exact hreserve x y h
  · intro w
    exact (hBg w).2.2
end Oberwolfach
