module

public import Oberwolfach.OrdinaryFixedVortexDeepCoverCommon

@[expose] public section
/-! Name the all-level robust deep-cover event for the actual fixed vortex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def OrdinaryFixedVortexDeepCoverEvent
    (m K d:ℕ) (a aLoad ρ θ:ℝ) (P:SimpleGraph V) (D vsize:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (j:Color) (σ:RawWheelOutcome V U Γ Color):Prop:=
  ∀i,i<Q.length→OrdinaryDeepCoverSeparateLoadEvent m K a aLoad ρ θ
    (P.comap (markedVortexVertexEmbedding Q i))
    ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
    (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d j
    (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)
end Oberwolfach
