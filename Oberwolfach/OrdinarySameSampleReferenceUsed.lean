module

public import Oberwolfach.OrdinaryOldApproximateAvoidsReference
public import Oberwolfach.OrdinaryReferenceUsedDegreeFromPlacement

@[expose] public section
/-! The old matching edges and the new bounded-degree placement are on the
same expanded sample, so the latter alone bounds reference consumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_reference_used_degree {n q:ℕ}
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (A B J:Fin q→Type) [∀u,Fintype (A u)] [∀u,DecidableEq (A u)]
    [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u)
      ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}))
    (ψ:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}→Fin n)
    (New:Fin q→Finset (Sym2 (Fin n)))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=((data u).deletedEdges.image (Sym2.map (ψ u)))∪New u)
    (hempty:∀u,IsEmpty (A u)) (hs:∀u,(data u).s₁=firstSumIndices)
    (Host P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (hdir:∀u,ActualOldImageDirected (data u) (ψ u)
      (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset)))
    (loss:ℝ) (hNew:∀x,((prescribedPhysicalUnion New).degree x:ℝ)≤loss):
    ∀x,((longPhysicalStateGraph P σ {0}⊓ordinaryEmbeddedComplements Fs C f).degree x:ℝ)≤loss:=by
  have hOld:∀u,Disjoint ((data u).deletedEdges.image (Sym2.map (ψ u))) (longPhysicalStateGraph P σ {0}).edgeFinset:=by
    intro u
    exact ordinary_old_approximate_edges_disjoint_reference (data u) (ψ u) (hempty u) (hs u) Host P Del π d σ (hdir u)
  exact ordinary_reference_used_degree_from_placement (longPhysicalStateGraph P σ {0}) Fs C f
    (fun u=>(data u).deletedEdges.image (Sym2.map (ψ u))) New hpartition hOld loss hNew
end Oberwolfach
