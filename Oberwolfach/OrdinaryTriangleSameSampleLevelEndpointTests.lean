module

public import Oberwolfach.OrdinaryTriangleBundledTestsNamedSplit

@[expose] public section
/-! The level, physical-parent and endpoint tests used by the selected
wheel certificates, all evaluated on one expanded sample and its coins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleSameSampleLevelEndpointTests
    {n q:ℕ} (D mv k d:ℕ) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Vor:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Vor.extendedVertices i↔x∈Vor.extendedVertices i)
    (α ρ₀ pstar βP ηP ηH βH cParent Bhost εTri δparent hParent pR pH κ aLoad εR εH
      bHub BHub ηHub capHub βeParent βhParent θhost tpot:ℝ)
    (sp:Fin q→Bool→ℝ)
    (weight:∀i,OrdinaryCycle (P.comap (markedVortexVertexEmbedding Vor i)) 3→ℝ)
    (endpointWeight:∀i,markedVortexVertexType Vor i→Sym2 (markedVortexVertexType Vor i⊕markedVortexHubType Vor i)→ℝ)
    (σx:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (coins:Sym2 (Fin n)→Bool):Prop :=
  let raw:=fun e=>expandedOrdinarySelectedCollapse e (σx e)
  let Bad:=permutationConflictGraph π (3*d)
  ∀i,i<Vor.length→
    OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Vor π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bhost εTri δparent hParent pR pH pstar κ aLoad εR εH
      bHub BHub ηHub capHub βeParent βhParent (fun _=>θhost+α-β/2)
      (fun t=>εR*(markedVortexInnerVertices Vor t).card) (fun t=>εH*(markedVortexInnerHubs Vor t).card)
      sp false raw coins i (weight i) ∧
    EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Vor i))
      (markedVortexInnerVertices Vor i) (markedVortexInnerVertices Vor i)ᶜ (endpointWeight i) ∧
    EndpointPhysicalPotentialEvent (P.comap (markedVortexVertexEmbedding Vor i))
      (Bad.comap (markedVortexVertexEmbedding Vor i)) (markedVortexInnerVertices Vor i) (markedVortexInnerHubs Vor i)
      (markedVortexInnerVertices Vor i)ᶜ (markedVortexPermutation Vor π hπ i) d false (endpointWeight i) pR pH tpot
      (ordinaryRawRestrictPair (markedVortexVertexEmbedding Vor i) (markedVortexHubEmbedding Vor i) raw)

theorem ordinary_triangle_same_sample_level_endpoint_tests_elim
    {n q:ℕ} (D mv k d:ℕ) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Vor:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Vor.extendedVertices i↔x∈Vor.extendedVertices i)
    (α ρ₀ pstar βP ηP ηH βH cParent Bhost εTri δparent hParent pR pH κ aLoad εR εH
      bHub BHub ηHub capHub βeParent βhParent θhost tpot:ℝ)
    (sp:Fin q→Bool→ℝ)
    (weight:∀i,OrdinaryCycle (P.comap (markedVortexVertexEmbedding Vor i)) 3→ℝ)
    (endpointWeight:∀i,markedVortexVertexType Vor i→Sym2 (markedVortexVertexType Vor i⊕markedVortexHubType Vor i)→ℝ)
    (σx:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (coins:Sym2 (Fin n)→Bool)
    (h:OrdinaryTriangleSameSampleLevelEndpointTests D mv k d β ε P Vor π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bhost εTri δparent hParent pR pH κ aLoad εR εH
      bHub BHub ηHub capHub βeParent βhParent θhost tpot sp weight endpointWeight σx coins):
    ∀i,i<Vor.length→
      OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Vor π hπ
        α ρ₀ pstar βP ηP ηH βH cParent Bhost εTri δparent hParent pR pH pstar κ aLoad εR εH
        bHub BHub ηHub capHub βeParent βhParent (fun _=>θhost+α-β/2)
        (fun t=>εR*(markedVortexInnerVertices Vor t).card) (fun t=>εH*(markedVortexInnerHubs Vor t).card)
        sp false (fun e=>expandedOrdinarySelectedCollapse e (σx e)) coins i (weight i) ∧
      EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Vor i))
        (markedVortexInnerVertices Vor i) (markedVortexInnerVertices Vor i)ᶜ (endpointWeight i) ∧
      EndpointPhysicalPotentialEvent (P.comap (markedVortexVertexEmbedding Vor i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Vor i))
        (markedVortexInnerVertices Vor i) (markedVortexInnerHubs Vor i)
        (markedVortexInnerVertices Vor i)ᶜ (markedVortexPermutation Vor π hπ i) d false (endpointWeight i) pR pH tpot
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Vor i) (markedVortexHubEmbedding Vor i)
          (fun e=>expandedOrdinarySelectedCollapse e (σx e))) :=by
  exact h
end Oberwolfach
