module

public import Oberwolfach.OrdinaryTriangleCommonSampleBundle
public import Oberwolfach.EndpointPhysicalParentWeights

@[expose] public section
/-! At every level, the fixed endpoint weights, endpoint potential test and
both row/index events are retained on the same expanded raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_common_sample_endpoint_rows
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (D vsize d:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (εR εH pR pH θsample κ αcut pmin δcap βe βh b Bweight ηHub tpot:ℝ)
    (s:U→Bool→ℝ) (j:Bool)
    (weight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ)
    (m aK bK:ℕ) (ξCorr:ℝ)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    (E:(Σσ,R σ)→Prop) (z:(Σσ,R σ)×(Sym2 (Fin n)→Bool))
    (hweights:∀i,i<Q.length→EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (markedVortexInnerVertices Q i)ᶜ (weight i))
    (h:OrdinaryTriangleCommonSampleBundle P D vsize d β ε Q π hπ εR εH pR pH θsample κ αcut pmin δcap
      βe βh b Bweight ηHub tpot s j weight m aK bK ξCorr E z)
    (i:ℕ) (hi:i<Q.length):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
    let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let ρi:=markedVortexPermutation Q π hπ i;
    EndpointPhysicalParentWeights (P.comap f) I Iᶜ (weight i) ∧
    EndpointPhysicalPotentialEvent (P.comap f) ((permutationConflictGraph π (3*d)).comap f)
      I B Iᶜ ρi d j (weight i) pR pH tpot (ordinaryRawRestrictPair f g raw) ∧
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D vsize β ε Q π hπ pR pH s j raw ∧
    OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D vsize β ε Q π hπ pR pH s j raw:=by
  intro raw f g I B ρi
  exact ⟨hweights i hi,h.1.2 i hi,h.1.1.1.1.1.2,h.1.1.1.1.1.1.2⟩
end Oberwolfach
