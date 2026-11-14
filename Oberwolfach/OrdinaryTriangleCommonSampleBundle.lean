module

public import Oberwolfach.OrdinaryTriangleVortexBufferedReservoirTwoStepSameSample
public import Oberwolfach.OrdinaryTriangleVortexBufferedConstructedReservoirBundleCapped
public import Oberwolfach.OrdinaryTriangleBufferedEndpointConstructedReservoirBundleCapped

@[expose] public section
/-! Name the triangle tests and corrected reservoir on one expanded outcome
and one family of reference coins, while retaining an arbitrary prior. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleCommonSampleBundle
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (D vsize d:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (εR εH pR pH θsample κ αcut pmin δcap βe βh b Bweight ηHub tpot:ℝ)
    (s:U→Bool→ℝ) (j:Bool)
    (weight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ)
    (m aK bK:ℕ) (ξCorr:ℝ)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    (E:(Σσ,R σ)→Prop) (z:(Σσ,R σ)×(Sym2 (Fin n)→Bool)):Prop :=
  let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)
  ((((((E z.1 ∧ OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D vsize β ε Q π hπ pR pH s j raw) ∧
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D vsize β ε Q π hπ pR pH s j raw) ∧
    OrdinaryFixedVortexTriangleNonrootCoverEvent d κ P D vsize β ε Q π hπ j raw) ∧
    (∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
      (sampledOrientation (rawWheelGraph P raw) z.2) αcut pmin)) ∧
    (∀i,i<Q.length→OrdinaryAdaptiveHubWeightsLevelEvent 2 (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
      pR pH θsample (εR*(markedVortexInnerVertices Q i).card) (εH*(markedVortexInnerHubs Q i).card)
      (2*((3*d:ℕ):ℝ)+δcap*min ((markedVortexInnerVertices Q i).card:ℝ) (markedVortexInnerHubs Q i).card)
      βe βh b Bweight ηHub (fun u=>s (markedVortexHubEmbedding Q i u)) j
      (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) raw))) ∧
    (∀i,i<Q.length→EndpointPhysicalPotentialEvent
      (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
      (markedVortexPermutation Q π hπ i) d j (weight i) pR pH tpot
      (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) raw))) ∧
    OrdinaryCorrectedProtectedReservoir 3 m (2*vsize) aK bK ξCorr (rawWheelGraph P raw\permutationConflictGraph π (3*d))
      (permutationConflictGraph π (3*d)) (rawWheelSpokes π d raw j)
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1)
end Oberwolfach
