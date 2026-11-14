module

public import Oberwolfach.OrdinaryTriangleSampleLevelsEndpointExistsProbability

@[expose] public section
/-! A selected inner/endpoint extension retains any prior on the same
expanded law, with its two explicit probability losses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleInnerEndpointExtension
    (n q D mv d:ℕ) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (p pH βeInner βhInner bInner BInner ηInner capInner tpot χinner χendpoint:ℝ)
    (density tR tH:ℕ→ℝ) (s:Fin q→Bool→ℝ) (j:Bool)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)]
    (μ:FiniteLaw (∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e))
    (ν:∀σ,FiniteLaw (R σ)) (κcoins:FiniteLaw (Sym2 (Fin n)→Bool)):Prop :=
    ∃endpointWeight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ,
      (∀i,i<Q.length→EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerVertices Q i)ᶜ (endpointWeight i)) ∧
    ∀(E:(Σσ,R σ)×(Sym2 (Fin n)→Bool)→Prop) (a:ℝ),
      1-a≤((μ.sigma ν).prod κcoins).probability E→
      1-a-χinner-χendpoint≤((μ.sigma ν).prod κcoins).probability (fun z=>
        (E z ∧ OrdinaryUniformInnerHubEvent 2 P D mv d β ε Q π hπ (2*p) pH βeInner βhInner
          bInner BInner ηInner capInner density tR tH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        ∀i,i<Q.length→EndpointPhysicalPotentialEvent (P.comap (markedVortexVertexEmbedding Q i))
          ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
          (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
          (markedVortexPermutation Q π hπ i) d j (endpointWeight i) (2*p) pH tpot
          (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
            (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))))
end Oberwolfach
