module

public import Oberwolfach.OrdinaryOrientedSpokeTransport
public import Oberwolfach.OrdinarySupportedRowCover

@[expose] public section
/-! Transfer row covers from an undirected bipartite host to the original
separate rim and hub domains, preserving their physical resource unions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq Z]

theorem ordinary_bipartite_row_cover_transfer
    (φ:V↪W) (ψ:U↪Z) (Q F:SimpleGraph W) (H:W→Z→Prop) (r:ℕ)
    (hQ:∀v w,Q.Adj v w→v∈Set.range φ ∧ w∈Set.range φ)
    (hH:∀v∈Set.range φ,∀u,H v u→u∈Set.range ψ)
    (M:Finset (OrdinaryWheel Q F H r)) (x:V) (A:Finset V) (K:ℕ)
    (hcover:OrdinaryRowCover M (φ x) (A.image φ) K):
    ∃ P:Finset (OrdinaryWheel (Q.comap φ) (F.comap φ) (fun v u=>H (φ v) (ψ u)) r),
      OrdinaryRowCover P x A K ∧
      (P.biUnion ordinaryWheelResources).image (ordinaryPairResourceEmbedding φ ψ)=
        M.biUnion ordinaryWheelResources:=by
  let H₀:=fun v u=>H (φ v) (ψ u)
  let H₁:=ordinaryMappedSpokes H₀ φ ψ
  let M':=M.image (ordinaryOrientedWheel φ ψ Q F H r hQ hH)
  have hc:OrdinaryRowCover M' (φ x) (A.image φ) K:=
    ordinary_oriented_row_cover φ ψ Q F H r hQ hH M x (A.image φ) K hcover
  have hf:∀v w,(F.comap φ).Adj v w→F.Adj (φ v) (φ w):=by intros;assumption
  obtain ⟨P,hP,hres⟩:=ordinary_row_cover_through_host_equalities φ ψ (Q.comap φ) (F.comap φ) Q F H₀ H₁ r
    (graph_comap_map_of_supported φ Q hQ) rfl hf M' x A K hc
  refine ⟨P,hP,?_⟩
  rw [hres]
  exact ordinary_oriented_packing_resources φ ψ Q F H r hQ hH M
end Oberwolfach
