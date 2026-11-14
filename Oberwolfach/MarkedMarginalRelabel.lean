module

public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.MarkedPermutationEmbedding

@[expose] public section
/-! The prescribed marginal of each typed resource is unchanged under a
permutation-compatible embedding, with the original density functions
restricted to the same hub. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq Z]

theorem raw_marked_marginal_relabel
    (f : W ↪ V) (g : Z → U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (P : SimpleGraph V) (d : ℕ)
    (p k : ℝ) (q : U → Γ → ℝ) (s : U → Color → ℝ) (a : Γ) (j : Color)
    (root : ((W×W)⊕(W×W))⊕(Bool×W×Z)) :
    rawMarkedWheelMarginal (P.comap f) ρ d p k (fun u => q (g u)) (fun u => s (g u)) a j root =
    rawMarkedWheelMarginal P π d p k q s a j
      (Sum.map (Sum.map (Prod.map f f) (Prod.map f f)) (Prod.map id (Prod.map f g)) root) := by
  cases root with
  | inl e =>
    cases e with
    | inl xy =>
      rcases xy with ⟨x,y⟩
      simp only [Sum.map_inl,Prod.map_apply,rawMarkedWheelMarginal,SimpleGraph.comap_adj,
        permutationClose_embedding_iff f ρ π hc]
    | inr xy =>
      rcases xy with ⟨x,y⟩
      simp only [Sum.map_inl,Sum.map_inr,Prod.map_apply,rawMarkedWheelMarginal,SimpleGraph.comap_adj,
        permutationClose_embedding_iff f ρ π hc, hc]
  | inr e =>
    rcases e with ⟨b,x,u⟩
    rfl
end Oberwolfach
