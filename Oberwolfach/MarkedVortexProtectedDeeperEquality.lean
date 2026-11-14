module

public import Oberwolfach.MarkedProtectedRestrictionEquality
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! Once the first inner pair is protected, the original and corrected
samples and spokes agree exactly at every deeper vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_vortex_protected_deeper_equality
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hrim:∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1→σ (Sum.inl e)=τ (Sum.inl e))
    (hinterval:∀e,σ (Sum.inr e)=τ (Sum.inr e))
    (hspoke:∀b v u,v∈Q.extendedVertices 1→u∈Q.extendedIndices 1→(H b v u↔H' b v u)):
    ∀ (i:ℕ), 1 ≤ i →
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ=
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) τ ∧
      (fun b v u=>H b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))=
      (fun b v u=>H' b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)):=by
  intro i hi
  exact marked_protected_restriction_equality σ τ H H' (Q.extendedVertices 1) (Q.extendedIndices 1)
    (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
    (fun x=>Q.extendedVertices_subset hi x.property) (fun u=>Q.extendedIndices_subset hi u.property)
    hrim hinterval hspoke
end Oberwolfach
