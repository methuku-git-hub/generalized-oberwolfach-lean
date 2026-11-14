module

public import Oberwolfach.MarkedEndpointLabelIdentities
public import Oberwolfach.MarkedNeighbourhoodEmbeddingGeometry

@[expose] public section

/-! Exact endpoint-label and spoke-neighbour counts on an invariant active
restriction. Both the direction and the marked tag are preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem markedEndpointLabels_embedding
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ) (A:Finset W)
    (σ:RawMarkedOutcome V U Γ Color) (a:Bool×Bool×W):
    markedEndpointLabels P π d (A.image f) (markedRowRequestEmbedding f.toEmbedding a) σ=
      (markedEndpointLabels (P.comap f) ρ d A a (rawMarkedRestrictPair f g σ)).image f:=by
  have hd:=markedRowDomain_image f π ρ hf P (3*d) A {a} ∅
  simp only [Finset.image_singleton,Finset.image_empty] at hd
  unfold markedEndpointLabels
  rw [hd,Finset.filter_image]
  apply congrArg (Finset.image f)
  apply Finset.filter_congr
  intro x hx
  rw [show markedRowRim (markedRowRequestEmbedding f.toEmbedding a) (f x)=
    Sum.map (Prod.map f f) (Prod.map f f) (markedRowRim a x) from markedRowRim_embedding f.toEmbedding a x]
  exact (rawMarkedRestrictPair_rims f g π ρ hf P d σ (markedRowRim a x)).symm

theorem markedEndpointLabels_embedding_card
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ) (A:Finset W)
    (σ:RawMarkedOutcome V U Γ Color) (mark incoming:Bool) (x:W):
    (markedEndpointLabels P π d (A.image f) (mark,incoming,f x) σ).card=
      (markedEndpointLabels (P.comap f) ρ d A (mark,incoming,x) (rawMarkedRestrictPair f g σ)).card:=by
  change (markedEndpointLabels P π d (A.image f)
    (markedRowRequestEmbedding f.toEmbedding (mark,incoming,x)) σ).card=_
  rw [markedEndpointLabels_embedding f g π ρ hf,Finset.card_image_of_injective _ f.injective]

theorem markedSpokeNeighbours_embedding_card
    (g:Z↪U) (B:Finset Z) (H:Bool→V→U→Prop) (mark:Bool) (x:V):
    ((B.image g).filter (H mark x)).card=(B.filter (fun u=>H mark x (g u))).card:=by
  rw [Finset.filter_image,Finset.card_image_of_injective _ g.injective]

end Oberwolfach
