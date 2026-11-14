module

public import Oberwolfach.MarkedVortexEncodedLaterLevels

@[expose] public section
/-! Complete later-level agreement consists of the identical raw outcome
and the identical physical spoke relations on the actual nested domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ}

theorem marked_vortex_encoded_later_agreement
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (E K:Type) (tail head:E→V) (ktail khead:K→V)
    (σ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop) (FS:SimpleGraph (V⊕U))
    (hS:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFS:∀ x∈Q.extendedVertices 1,∀ u∈Q.extendedIndices 1,¬FS.Adj (Sum.inl x) (Sum.inr u)):
    ∀ i,1 ≤ i →
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
        (rawMarkedEncodeHost tail head ktail khead π σ (Q.extendedVertices 1))=
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ ∧
      (fun b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>
        H b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))=
      (fun b v u=>H' b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)) := by
  intro i hi
  refine ⟨marked_vortex_encoded_later_levels Q π E K tail head ktail khead σ i hi,?_⟩
  funext b v u
  apply propext
  by_contra hh
  exact hFS v.val (Q.extendedVertices_subset hi v.property)
    u.val (Q.extendedIndices_subset hi u.property) (hS b v.val u.val hh)
end Oberwolfach
