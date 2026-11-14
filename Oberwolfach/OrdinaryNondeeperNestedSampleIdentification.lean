module

public import Oberwolfach.OrdinaryRawPairRestrictionComposition
public import Oberwolfach.OrdinaryNondeeperIntoParent

@[expose] public section
/-! The nested local outcome and host are exactly the direct restrictions
of the same ambient sample and host to the nondeeper pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_nondeeper_nested_sample_identification
    (P G:SimpleGraph V) (Hs:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (i:ℕ) (σ:RawWheelOutcome V U Γ Color):
    let f₁:markedVortexVertexType Q i↪V:=(markedVortexVertexEmbedding Q i).toEmbedding
    let g₁:markedVortexHubType Q i↪U:=markedVortexHubEmbedding Q i
    let f₂:=ordinaryNondeeperVertexToParent Q i
    let g₂:=ordinaryNondeeperHubToParent Q i
    let f:=ordinaryVortexNondeeperVertexEmbedding Q i
    let g:=ordinaryVortexNondeeperHubEmbedding Q i;
    ordinaryRawRestrictPair f₂ g₂ (ordinaryRawRestrictPair f₁ g₁ σ)=ordinaryRawRestrictPair f g σ ∧
    (P.induce ((Q.extendedVertices i):Set V)).comap f₂=P.comap f ∧
    (G.induce ((Q.extendedVertices i):Set V)).comap f₂=G.comap f ∧
    (fun v u=>Hs (f₁ (f₂ v)) (g₁ (g₂ u)))=(fun v u=>Hs (f v) (g u)) :=by
  intro f₁ g₁ f₂ g₂ f g
  refine ⟨?_,?_,?_,?_⟩
  · rw [ordinary_raw_pair_restriction_comp,ordinary_nondeeper_vertex_embedding_composition,
      ordinary_nondeeper_hub_embedding_composition]
  · ext x y
    rfl
  · ext x y
    rfl
  · rfl
end Oberwolfach
