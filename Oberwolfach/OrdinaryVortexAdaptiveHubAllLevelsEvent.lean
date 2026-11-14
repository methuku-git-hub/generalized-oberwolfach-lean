module

public import Oberwolfach.OrdinaryExpandedVortexBufferedHubTraceCapBundleBounded

@[expose] public section
/-! Name the simultaneous adaptive hub-weight events at all vortex levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryVortexAdaptiveHubAllLevelsEvent
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (m d D mv:ℕ) (β ε p pH δcap b Bweight ηHub:ℝ) (density tR tH βe βh:ℕ→ℝ)
    (P:SimpleGraph V) (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color):Prop :=
    ∀i,i<Q.length→
      OrdinaryAdaptiveHubWeightsLevelEvent m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
        (2*p) pH (density i) (tR i) (tH i)
        (2*((3*d:ℕ):ℝ)+δcap*min ((markedVortexInnerVertices Q i).card:ℝ) (markedVortexInnerHubs Q i).card)
        (βe i) (βh i) b Bweight ηHub (fun z=>s (markedVortexHubEmbedding Q i z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) raw)
end Oberwolfach
