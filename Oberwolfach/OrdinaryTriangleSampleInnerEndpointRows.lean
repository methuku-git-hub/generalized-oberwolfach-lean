module

public import Oberwolfach.OrdinaryTriangleCommonSampleEndpointRows
public import Oberwolfach.OrdinaryTriangleUniformInnerHubEvent

@[expose] public section
/-! On the same expanded outcome, expose each level's original endpoint
weights and raw rows together with its all-edit inner hub callback. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_sample_inner_endpoint_rows
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (D vsize d:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (εR εH pR pH θsample κ αcut pmin δcap βe βh b Bweight ηHub tpot:ℝ)
    (bInner BInner ηInner cap:ℝ) (s:U→Bool→ℝ) (j:Bool)
    (weight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ)
    (m aK bK:ℕ) (ξCorr:ℝ)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    (E:(Σσ,R σ)→Prop) (z:(Σσ,R σ)×(Sym2 (Fin n)→Bool))
    (hweights:∀i,i<Q.length→EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (markedVortexInnerVertices Q i)ᶜ (weight i))
    (h:OrdinaryTriangleCommonSampleBundle P D vsize d β ε Q π hπ εR εH pR pH θsample κ αcut pmin δcap
      βe βh b Bweight ηHub tpot s j weight m aK bK ξCorr E z)
    (hInner:OrdinaryTriangleUniformInnerHubEvent P D vsize d β ε Q π hπ pR pH βe βh bInner BInner ηInner cap
      (fun _=>θsample) (fun i=>εR*(markedVortexInnerVertices Q i).card)
      (fun i=>εH*(markedVortexInnerHubs Q i).card) s j
      (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))
    (i:ℕ) (hi:i<Q.length):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
    let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let ρi:=markedVortexPermutation Q π hπ i;
    EndpointPhysicalParentWeights (P.comap f) I Iᶜ (weight i) ∧
    EndpointPhysicalPotentialEvent (P.comap f) ((permutationConflictGraph π (3*d)).comap f)
      I B Iᶜ ρi d j (weight i) pR pH tpot (ordinaryRawRestrictPair f g raw) ∧
    RawOrdinaryRows (P.comap f) ρi d 3 I pR (fun u=>s (g u)) j (εR*I.card)
      (ordinaryRawRestrictPair f g raw) ∧
    (∀Lold:ℝ,0≤Lold→Lold≤cap*I.card→
      OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent 2 (P.comap f)
        ((permutationConflictGraph π (3*d)).comap f) I B ρi d pR pH θsample
        (εR*I.card) (εH*B.card) Lold βe βh bInner BInner ηInner
        (fun u=>s (g u)) j (ordinaryRawRestrictPair f g raw)) :=by
  intro raw f g I B ρi
  have he:=ordinary_triangle_common_sample_endpoint_rows P D vsize d β ε Q π hπ εR εH pR pH θsample κ αcut pmin δcap
    βe βh b Bweight ηHub tpot s j weight m aK bK ξCorr E z hweights h i hi
  have hr:RawOrdinaryRows (P.comap f) ρi d 3 I pR (fun u=>s (g u)) j (εR*I.card)
      (ordinaryRawRestrictPair f g raw):=by
    convert (he.2.2.1 i hi).1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  exact ⟨he.1,he.2.1,hr,hInner i hi⟩
end Oberwolfach
