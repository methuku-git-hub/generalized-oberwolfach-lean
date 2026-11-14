module

public import Oberwolfach.OrdinaryFixedVortexTriangleNonrootCoverCommon

@[expose] public section
/-! Name the all-level triangle outer-degree cover event on a fixed vortex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

def OrdinaryFixedVortexTriangleNonrootCoverEvent
    (d:ℕ) (κ:ℝ) (P:SimpleGraph V) (D vsize:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (j:Color) (σ:RawWheelOutcome V U Γ Color):Prop:=
  ∀i,i<Q.length→OrdinaryTriangleFiniteCoverNonrootDegreeEvent κ
    (P.comap (markedVortexVertexEmbedding Q i))
    ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
    (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d j
    (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)
end Oberwolfach
