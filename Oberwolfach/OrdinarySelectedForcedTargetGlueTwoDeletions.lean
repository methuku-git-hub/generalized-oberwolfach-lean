module

public import Oberwolfach.OrdinaryForcedTargetsResidualGlue
public import Oberwolfach.OrdinaryEmptyFinalPhysicalTarget
public import Oberwolfach.OrdinarySelectedRequiredDirectedTarget
public import Oberwolfach.OrdinaryOldFamilyAvoidsRequired
public import Oberwolfach.ResidualActualEdgePartition

@[expose] public section
/-! Glue the reserved-list forced placement to the old matching embedding and
obtain whole unreserved-factor embeddings in the edited target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selected_forced_target_glue_two_deletions
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n)
    {X A B J:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,Fintype (A u)] [∀u,DecidableEq (A u)] [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (P Host DelMatch DelFinish Target G:SimpleGraph (Fin n)) (hHost:Host≤P) (hG:G≤Target)
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hOldTarget:∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) DelMatch.edgeFinset) x y→Target.Adj x y)
    (hFinishTarget:∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→
      ¬DelFinish.Adj x y→Target.Adj x y)
    (hempty:∀u,IsEmpty (A u)) (len:∀u,A u→ℕ) (inner:∀u (i:A u),Fin (len u i+1)↪X u)
    (F:∀u,SimpleGraph (X u)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u) (F u))
    (hs:∀u,(data u).s₁=firstSumIndices)
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (Old:∀u,Finset (X u))
    (hOldEq:∀u,Old u=(data u).oldDomain\bufferedPathStrictInterior (len u) (inner u))
    (ψ:∀u,X u→Fin n) (hψ:∀u,Set.InjOn (ψ u) (↑(Old u):Set (X u)))
    (hdir:∀u,ActualOldImageDirected (data u) (ψ u)
      (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) DelMatch.edgeFinset)))
    (hOO:∀u v,u≠v→Disjoint ((data u).deletedEdges.image (Sym2.map (ψ u))) ((data v).deletedEdges.image (Sym2.map (ψ v))))
    (hOG:∀u,Disjoint ((data u).deletedEdges.image (Sym2.map (ψ u))) G.edgeFinset)
    (L T:U→Finset (Fin n)) (hL:∀u,Disjoint (L u) ((Old u).image (ψ u)))
    (pieces:∀u,List (PrescribedSourcePiece {x // x∈(data u).remaining}))
    (hgraph:∀u,prescribedDependentGraph pieces u=((data u).graph).induce (↑(data u).remaining:Set (X u)))
    (M:U→Finset (Fin n×Fin n))
    (Bset:∀u,Finset {x // x∈(data u).remaining}) (g Φ:∀u,{x // x∈(data u).remaining}→Fin n)
    (hinj:∀u,Function.Injective (Φ u))
    (hB:∀u,residualSubtypeSet (data u).remaining (data u).prescribed⊆Bset u ∧
      (∀x∈residualSubtypeSet (data u).remaining (data u).prescribed,g u x=ψ u x.1) ∧
      (Bset u).image (g u)=
        (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1)∪
        prescribedMatchingEndpoints (M u)∪((T u\(Old u).image (ψ u))\prescribedMatchingEndpoints (M u)) ∧
      (prescribedInducedArcs (prescribedDependentDigraph pieces u) (Bset u)).image (Prod.map (g u) (g u))=M u)
    (hOldM:∀u,Disjoint ((Old u).image (ψ u)) (prescribedMatchingEndpoints (M u)))
    (hTcover:∀u v,v∈T u→v∈(Old u).image (ψ u)∨∃x,Φ u x=v)
    (hΦg:∀u x,x∈Bset u→Φ u x=g u x)
    (hΦL:∀u x,x∉Bset u→Φ u x∈L u)
    (hΦarc:∀u x y,prescribedDependentDigraph pieces u x y→
      (rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) (Φ u x) (Φ u y) ∧ ¬DelFinish.Adj (Φ u x) (Φ u y) ∨ G.Adj (Φ u x) (Φ u y)) ∧
      ((x∉Bset u ∨ y∉Bset u)→ rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) (Φ u x) (Φ u y) ∧ ¬DelFinish.Adj (Φ u x) (Φ u y)))
    (hMsub:∀u,(M u).image prescribedArcPhysical⊆G.edgeFinset)
    (hEpair:PairwisePhysicalDisjoint (fun u=>((prescribedDependentGraph pieces u).edgeFinset).image (Sym2.map (Φ u)))):
    ∃f:∀u,X u↪Fin n,
      (∀u x,x∈(data u).oldDomain→f u x=ψ u x) ∧
      (∀u (x:{x // x∈(data u).remaining}),f u x.1=Φ u x) ∧
      (∀u v,v∈T u→∃x,f u x=v) ∧
      (∀u x y,(F u).Adj x y→Target.Adj (f u x) (f u y)) ∧
      (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (X u) (F u) (f u))
        (partialFactorPhysicalEdgesPoly (X v) (F v) (f v))) :=by
  letI:Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  obtain ⟨f,hfold,hfnew,hfcover⟩:=empty_final_dependent_residual_glue_with_forced_targets hempty len inner F hF data hCycle Old hOldEq ψ hψ Bset g Φ L
    (fun u=>prescribedMatchingEndpoints (M u)) T (fun u=>(hB u).1) hinj (fun u=>(hB u).2.1) hΦg
    (fun u=>(hB u).2.2.1) hOldM hTcover hΦL hL
  have hpartition:∀u,((F u).edgeFinset).image (Sym2.map (f u))=
      (data u).deletedEdges.image (Sym2.map (ψ u)) ∪
        (((data u).graph.induce (fun x=>x∈(data u).remaining)).edgeFinset).image (Sym2.map (Φ u)):=by
    intro u
    have hh:=(data u).glued_factor_edge_images (hF u) (hCycle u) (ψ u) (f u) (Φ u) (hfold u) (hfnew u)
    convert hh using 1 <;> congr 2 <;> apply graph_edge_finset_instance_eq
  have hgraphEdges:∀u,(prescribedDependentGraph pieces u).edgeFinset=
      ((data u).graph.induce (fun x=>x∈(data u).remaining)).edgeFinset:=by
    intro u
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [hgraph u]
    rfl
  have hpart:∀u,((F u).edgeFinset).image (Sym2.map (f u))=
      (data u).deletedEdges.image (Sym2.map (ψ u)) ∪
        ((prescribedDependentGraph pieces u).edgeFinset).image (Sym2.map (Φ u)):=by
    intro u
    rw [hgraphEdges u]
    exact hpartition u
  let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬DelFinish.Adj x y
  let Dstar:=fun x y=>Dfree x y ∨ G.Adj x y
  have hstar:∀x y,Dstar x y→Target.Adj x y:=by
    intro x y h
    rcases h with h|h
    · exact hFinishTarget x y h.1 h.2
    · exact hG h
  have hselected:∀x y,Dfree x y→ rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y:=fun _ _ h=>h.1
  have hinst:ordinaryEmptyPhysicalTargetFin n=instDecidableEqFin n:=Subsingleton.elim _ _
  have hcomplete:=ordinary_empty_final_physical_target_completion (n:=n) (U:=U) (X:=X) (A:=A) (B:=B) (J:=J)
  rw [hinst] at hcomplete
  obtain ⟨hhost,hdisjoint⟩:=hcomplete P Host DelMatch Target hHost π d σ hOldTarget
    F data hempty hs ψ (fun u=>(f u:X u→Fin n)) pieces Bset g Φ M G _ _ hstar hselected hdir
    hΦg (fun u=>(hB u).2.2.2) hΦarc hMsub hpart hOO hOG hEpair
  exact ⟨f,hfold,hfnew,hfcover,hhost,hdisjoint⟩
end Oberwolfach
