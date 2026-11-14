module

public import Oberwolfach.MarkedNeighbourhoodEmbeddingGeometry

@[expose] public section

/-! Counts on embedded fixed domains agree exactly, retaining directions,
spoke types, all request roots, and the parent comparison graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem markedRowCountWithSpokes_embedding
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset W) (S:Finset (Bool×Bool×W)) (J:Finset (Bool×Z)):
    markedRowCountWithSpokes P π d σ H (C.image f)
      (S.image (markedRowRequestEmbedding f.toEmbedding))
      (J.image ((Function.Embedding.refl Bool).prodMap g))=
    markedRowCountWithSpokes (P.comap f) ρ d (rawMarkedRestrictPair f g σ)
      (fun b x u=>H b (f x) (g u)) C S J:=by
  have hR (a:Bool×Bool×W) (x:W):
      rawMarkedPairRims P π d σ (markedRowRim (markedRowRequestEmbedding f.toEmbedding a) (f x))↔
      rawMarkedPairRims (P.comap f) ρ d (rawMarkedRestrictPair f g σ) (markedRowRim a x):=by
    rw [show markedRowRim (markedRowRequestEmbedding f.toEmbedding a) (f x)=
      Sum.map (Prod.map f f) (Prod.map f f) (markedRowRim a x) from markedRowRim_embedding f.toEmbedding a x]
    exact (rawMarkedRestrictPair_rims f g π ρ hf P d σ (markedRowRim a x)).symm
  unfold markedRowCountWithSpokes
  rw [Finset.sum_image (fun _ _ _ _ he=>f.injective he)]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  simp only [Finset.forall_mem_image,hR,Function.Embedding.coe_prodMap,Prod.map_apply,Function.Embedding.refl_apply]
  rfl

theorem markedIndexCountWithSpokes_embedding
    (f:W↪V) (g:Z↪U) (H:Bool→V→U→Prop) (B:Finset Z) (J:Finset (Bool×W)):
    markedIndexCountWithSpokes H (B.image g) (J.image ((Function.Embedding.refl Bool).prodMap f))=
      markedIndexCountWithSpokes (fun b x u=>H b (f x) (g u)) B J:=by
  unfold markedIndexCountWithSpokes
  rw [Finset.sum_image (fun _ _ _ _ he=>g.injective he)]
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  simp only [Finset.forall_mem_image,Function.Embedding.coe_prodMap,Prod.map_apply,Function.Embedding.refl_apply]
  rfl

end Oberwolfach
