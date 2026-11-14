module

public import Oberwolfach.MarkedVortexRestrictionChain
public import Oberwolfach.MarkedHostRawEncoding

@[expose] public section
/-! The encoded prepared host retains the complete raw sampled outcome on
each later vortex level, not only the visible typed rim predicates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ}

theorem marked_vortex_encoded_later_levels
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (E K:Type) (tail head:E→V) (ktail khead:K→V)
    (σ:RawMarkedOutcome V U Γ Color):
    ∀ i,1 ≤ i →
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
        (rawMarkedEncodeHost tail head ktail khead π σ (Q.extendedVertices 1))=
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ := by
  intro i hi
  exact rawMarkedEncodeHost_restrict tail head ktail khead π σ (Q.extendedVertices 1)
    (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
    (fun x=>Q.extendedVertices_subset hi x.property)
end Oberwolfach
