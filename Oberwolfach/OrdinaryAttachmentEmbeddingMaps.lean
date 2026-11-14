module

public import Oberwolfach.OrdinaryExpansionEmbeddingMaps
public import Oberwolfach.OrdinaryFiniteAttachments

@[expose] public section

/-! Preserve old edges and identify the actual host edges of each
attached wheel under the injective row and hub maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
variable {V₀ U₀ V U I W : Type*}

theorem attachmentRowEmbedding_hom (φ : V₀ ↪ V) (f : I → W ↪ V)
    (hroot : ∀ i w v,f i w≠φ v) (hsep : ∀ i j,i≠j → ∀ a b,f i a≠f j b)
    (G₀ : SimpleGraph V₀) (C : SimpleGraph W) (z : W) (ρ : I → V₀) (G : SimpleGraph V)
    (hold : ∀ a b,G₀.Adj a b → G.Adj (φ a) (φ b))
    (hcycle : ∀ i w w',w≠z → w'≠z → C.Adj w w' → G.Adj (f i w) (f i w'))
    (hcross : ∀ i w,C.Adj z w → G.Adj (φ (ρ i)) (f i w)) :
    ∀ a b,(ordinaryAttachmentRim G₀ C z ρ).Adj a b →
      G.Adj (expansionRowEmbedding φ f hroot hsep a) (expansionRowEmbedding φ f hroot hsep b) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact hold a b h
    | inr p =>
      rcases p with ⟨i,w⟩
      change ρ i=a ∧ w≠z ∧ C.Adj z w at h
      rcases h with ⟨rfl,_,hc⟩
      exact hcross i w hc
  | inr p =>
    rcases p with ⟨i,w⟩
    cases b with
    | inl b =>
      change ρ i=b ∧ w≠z ∧ C.Adj z w at h
      rcases h with ⟨rfl,_,hc⟩
      exact (hcross i w hc).symm
    | inr p =>
      rcases p with ⟨j,w'⟩
      change i=j ∧ w≠z ∧ w'≠z ∧ C.Adj w w' at h
      obtain ⟨rfl,hw,hw',hc⟩ := h
      exact hcycle i w w' hw hw' hc

theorem attachmentEmbedding_spokes (φ : V₀ ↪ V) (f : I → W ↪ V)
    (hroot : ∀ i w v,f i w≠φ v) (hsep : ∀ i j,i≠j → ∀ a b,f i a≠f j b)
    (ψ : U₀ ↪ U) (a : I → U) (huroot : ∀ i u,a i≠ψ u) (husep : Function.Injective a)
    (H₀ : V₀ → U₀ → Prop) (z : W) (ρ : I → V₀) (H : V → U → Prop)
    (hold : ∀ v u,H₀ v u → H (φ v) (ψ u))
    (hH : ∀ i w,w≠z → H (f i w) (a i)) (hcross : ∀ i,H (φ (ρ i)) (a i)) :
    ∀ b c,ordinaryAttachmentSpokes H₀ z ρ b c →
      H (expansionRowEmbedding φ f hroot hsep b) (expansionHubEmbedding ψ a huroot husep c) := by
  intro b c h
  cases b with
  | inl b =>
    cases c with
    | inl c => exact hold b c h
    | inr i =>
      change ρ i=b at h
      subst b
      exact hcross i
  | inr p =>
    rcases p with ⟨i,w⟩
    cases c with
    | inl c => exact False.elim h
    | inr j =>
      change w≠z ∧ i=j at h
      obtain ⟨hw,rfl⟩ := h
      exact hH i w hw

end Oberwolfach
