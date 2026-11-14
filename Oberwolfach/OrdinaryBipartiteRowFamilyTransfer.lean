module

public import Oberwolfach.OrdinaryBipartiteRowCoverTransfer

@[expose] public section
/-! All row covers use the same embeddings; their cross-row resource
disjointness therefore survives restriction to the original domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq Z]

theorem ordinary_bipartite_row_family_transfer
    (φ:V↪W) (ψ:U↪Z) (Q F:SimpleGraph W) (H:W→Z→Prop) (r n:ℕ)
    (hQ:∀v w,Q.Adj v w→v∈Set.range φ ∧ w∈Set.range φ)
    (hH:∀v∈Set.range φ,∀u,H v u→u∈Set.range ψ)
    (M:Fin n→Finset (OrdinaryWheel Q F H r)) (x:Fin n→V) (A:Finset V) (K:ℕ)
    (hcover:∀i,OrdinaryRowCover (M i) (φ (x i)) (A.image φ) K)
    (hcross:∀i j,i≠j→Disjoint ((M i).biUnion ordinaryWheelResources) ((M j).biUnion ordinaryWheelResources)):
    ∃ P:Fin n→Finset (OrdinaryWheel (Q.comap φ) (F.comap φ) (fun v u=>H (φ v) (ψ u)) r),
      (∀i,OrdinaryRowCover (P i) (x i) A K) ∧
      (∀i j,i≠j→Disjoint ((P i).biUnion ordinaryWheelResources) ((P j).biUnion ordinaryWheelResources)) ∧
      (∀i,((P i).biUnion ordinaryWheelResources).image (ordinaryPairResourceEmbedding φ ψ)=
        (M i).biUnion ordinaryWheelResources):=by
  have hex:∀i,∃P:Finset (OrdinaryWheel (Q.comap φ) (F.comap φ) (fun v u=>H (φ v) (ψ u)) r),
      OrdinaryRowCover P (x i) A K ∧
      (P.biUnion ordinaryWheelResources).image (ordinaryPairResourceEmbedding φ ψ)=
        (M i).biUnion ordinaryWheelResources:=
    fun i=>ordinary_bipartite_row_cover_transfer φ ψ Q F H r hQ hH (M i) (x i) A K (hcover i)
  choose P hP hres using hex
  refine ⟨P,hP,?_,hres⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have hi:(ordinaryPairResourceEmbedding φ ψ) a∈(M i).biUnion ordinaryWheelResources:=by
    rw [←hres i]
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hj:(ordinaryPairResourceEmbedding φ ψ) a∈(M j).biUnion ordinaryWheelResources:=by
    rw [←hres j]
    exact Finset.mem_image.mpr ⟨a,hb,rfl⟩
  exact Finset.disjoint_left.mp (hcross i j hij) hi hj
end Oberwolfach
