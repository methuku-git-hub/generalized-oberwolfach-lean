module

public import Oberwolfach.OrdinaryOldEdgesApproximateLayer
public import Oberwolfach.DependentResidualAvoidsOldEdges
public import Oberwolfach.DependentGluedHostAndDisjoint
public import Oberwolfach.DependentResidualDirectedHost

@[expose] public section
/-! Same-sample old and residual physical edges combine into pairwise
edge-disjoint whole-source embeddings once the bad edges avoid the old pack. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryEmptyPhysicalTargetFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_empty_final_physical_target_completion
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X A B J:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,Fintype (A u)] [∀u,DecidableEq (A u)] [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (P H Del Target:SimpleGraph (Fin n)) (hHP:H≤P) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hOldTarget:∀x y,rawMixedPhysicalArc H π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→Target.Adj x y)
    (F:∀u,SimpleGraph (X u)) (data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u) (F u))
    (hempty:∀u,IsEmpty (A u)) (hs:∀u,(data u).s₁=firstSumIndices)
    (ψ:∀u,X u→Fin n) (f:∀u,X u→Fin n)
    (pieces:∀u,List (PrescribedSourcePiece {x // x∈(data u).remaining}))
    (Bset:∀u,Finset {x // x∈(data u).remaining}) (g Φ:∀u,{x // x∈(data u).remaining}→Fin n)
    (M:U→Finset (Fin n×Fin n)) (G:SimpleGraph (Fin n))
    (Dstar Dfree:Fin n→Fin n→Prop)
    (hstar:∀x y,Dstar x y→Target.Adj x y)
    (hselected:∀x y,Dfree x y→ rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y)
    (hdir:∀u,ActualOldImageDirected (data u) (ψ u)
      (rawMixedPhysicalArc H π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset)))
    (hΦ:∀u x,x∈Bset u→Φ u x=g u x)
    (hM:∀u,(prescribedInducedArcs (prescribedDependentDigraph pieces u) (Bset u)).image (Prod.map (g u) (g u))=M u)
    (harc:∀u x y,prescribedDependentDigraph pieces u x y→Dstar (Φ u x) (Φ u y) ∧
      ((x∉Bset u ∨ y∉Bset u)→Dfree (Φ u x) (Φ u y)))
    (hMsub:∀u,(M u).image prescribedArcPhysical⊆G.edgeFinset):
    let Old:=fun u=>(data u).deletedEdges.image (Sym2.map (ψ u))
    let New:=fun u=>((prescribedDependentGraph pieces u).edgeFinset).image (Sym2.map (Φ u));
    (∀u,((F u).edgeFinset).image (Sym2.map (f u))=Old u∪New u)→
    (∀u v,u≠v→Disjoint (Old u) (Old v))→
    (∀u,Disjoint (Old u) G.edgeFinset)→
    PairwisePhysicalDisjoint New→
    (∀u x y,(F u).Adj x y→Target.Adj (f u x) (f u y)) ∧
    (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (X u) (F u) (f u))
      (partialFactorPhysicalEdgesPoly (X v) (F v) (f v))):=by
  intro Old New hpart hOO hOG hNN
  have hOldApprox:∀u,Old u⊆(longApproximatePhysicalGraph P π d σ).edgeFinset:=by
    intro u
    simpa only [Old] using ordinary_old_edges_in_approximate_layer P H Del hHP π d σ (data u) (hempty u) (hs u) (ψ u) (hdir u)
  have hOldHost:∀u,Old u⊆Target.edgeFinset:=by
    intro u
    apply actual_old_directed_host_with_empty_final (data u) (hempty u) (hs u) (ψ u) Target
      (rawMixedPhysicalArc H π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset))
    · intro x y h
      exact hOldTarget x y h
    · exact hdir u
  have hNewHost:∀u,New u⊆Target.edgeFinset:=
    prescribed_dependent_residual_images_in_host pieces Φ Target Dstar hstar (fun u x y h=>(harc u x y h).1)
  have hMatchOld:∀u v,Disjoint (Old v) ((M u).image prescribedArcPhysical):=fun u v=>(hOG v).mono_right (hMsub u)
  have hFreeOld:=selected_free_avoids_old_approximate_edges P π d σ Old hOldApprox Dfree hselected
  have hON:∀u v,Disjoint (Old u) (New v):=by
    intro u v
    exact prescribed_dependent_residual_avoids_old_edges pieces Bset g Φ M Dfree hΦ hM
      (fun u x y h=>(harc u x y h).2) Old hMatchOld hFreeOld v u
  exact dependent_glued_factor_host_and_disjoint F Target f Old New hpart hOldHost hNewHost hOO hON hNN
end Oberwolfach
