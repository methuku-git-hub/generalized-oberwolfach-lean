module

public import Oberwolfach.OrdinaryEmbeddedRowCover
public import Oberwolfach.OrdinaryEmbeddedHostRecovery

@[expose] public section
/-! A row cover whose rim and spoke hosts are supported in fixed embedded
vertex and hub domains restricts to the original types on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq Z]

theorem ordinary_row_cover_through_host_equalities
    (φ:V↪W) (ψ:U↪Z) (G F₀:SimpleGraph V) (Q F:SimpleGraph W)
    (H₀:V→U→Prop) (H:W→Z→Prop) (r:ℕ)
    (hq:G.map φ=Q) (hs:ordinaryMappedSpokes H₀ φ ψ=H)
    (hF:∀v w,F₀.Adj v w→F.Adj (φ v) (φ w))
    (M:Finset (OrdinaryWheel Q F H r)) (x:V) (A:Finset V) (K:ℕ)
    (hcover:OrdinaryRowCover M (φ x) (A.image φ) K):
    ∃ P:Finset (OrdinaryWheel G F₀ H₀ r),OrdinaryRowCover P x A K ∧
      (P.biUnion ordinaryWheelResources).image (ordinaryPairResourceEmbedding φ ψ)=M.biUnion ordinaryWheelResources:=by
  subst Q
  subst H
  let P:=M.image (ordinaryEmbeddedWheelPullback φ ψ G F₀ F H₀ r hF)
  exact ⟨P,ordinary_embedded_row_cover φ ψ G F₀ F H₀ r hF M x A K hcover,
    ordinary_embedded_packing_resources φ ψ G F₀ F H₀ r hF M⟩

theorem ordinary_supported_row_cover
    (φ:V↪W) (ψ:U↪Z) (Q F:SimpleGraph W) (H:W→Z→Prop) (r:ℕ)
    (hQ:∀v w,Q.Adj v w→v∈Set.range φ ∧ w∈Set.range φ)
    (hH:∀v u,H v u→v∈Set.range φ ∧ u∈Set.range ψ)
    (M:Finset (OrdinaryWheel Q F H r)) (x:V) (A:Finset V) (K:ℕ)
    (hcover:OrdinaryRowCover M (φ x) (A.image φ) K):
    ∃ P:Finset (OrdinaryWheel (Q.comap φ) (F.comap φ) (fun v u=>H (φ v) (ψ u)) r),
      OrdinaryRowCover P x A K ∧
      (P.biUnion ordinaryWheelResources).image (ordinaryPairResourceEmbedding φ ψ)=
        M.biUnion ordinaryWheelResources:=by
  apply ordinary_row_cover_through_host_equalities φ ψ (Q.comap φ) (F.comap φ) Q F
    (fun v u=>H (φ v) (ψ u)) H r
    (graph_comap_map_of_supported φ Q hQ) (ordinary_mapped_spokes_of_supported φ ψ H hH)
  · intros;assumption
  · exact hcover
end Oberwolfach
