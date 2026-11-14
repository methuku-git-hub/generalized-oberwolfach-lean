module

public import Oberwolfach.OrdinaryExpandedUniformEditEventWithSetups

@[expose] public section
/-! A name for the all-level triangle inner-weight event attached to an
arbitrary earlier expanded-sample prior. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def OrdinaryUniformInnerHubEvent
    (mWheel:ℕ) (P:SimpleGraph V) (D mv d:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (pR pH βe βh b B η cap:ℝ) (density tR tH:ℕ→ℝ) (s:U→Color→ℝ) (j:Color)
    (σ:RawWheelOutcome V U Γ Color):Prop:=
  ∀i,i<Q.length→∀Lold:ℝ,0≤Lold→Lold≤cap*(markedVortexInnerVertices Q i).card→
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent mWheel (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
      pR pH (density i) (tR i) (tH i) Lold βe βh b B η
      (fun u=>s (markedVortexHubEmbedding Q i u)) j
      (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)
end Oberwolfach
