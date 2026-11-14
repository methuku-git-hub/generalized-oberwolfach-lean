module

public import Oberwolfach.OrdinaryTriangleParentUniformSampleInputs
public import Oberwolfach.OrdinaryUniformInnerHubEvent

@[expose] public section
/-! Triangle certificate inputs at one level, with the inner-scale hub event
and all reference, fine-cover and row tests taken from one physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleSelectedSampleLevelData
    (n q D mv k d:ℕ) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href:ℝ)
    (pR pH pmin κ aLoad εR εH bInner BInner ηInner capInner βe βh:ℝ)
    (density tR tH:ℕ→ℝ) (s:Fin q→Bool→ℝ) (j:Bool)
    (raw:RawWheelOutcome (Fin n) (Fin q) Bool Bool) (coins:Sym2 (Fin n)→Bool) (i:ℕ)
    (weight:OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q i)) 3→ℝ):Prop :=
    let Fconf:=permutationConflictGraph π (3*d)
    let f:=(markedVortexVertexEmbedding Q i).toEmbedding
    let g:=markedVortexHubEmbedding Q i
    let ρi:=markedVortexPermutation Q π hπ i;
    OrdinaryUniformInnerHubEvent 2 P D mv d β ε Q π hπ pR pH βe βh
      bInner BInner ηInner capInner density tR tH s j raw ∧
    OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D mv β ε Q π hπ j raw ∧
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ pR pH s j raw ∧
    OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ pR pH s j raw ∧
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1)) (sampledOrientation (rawWheelGraph P raw) coins) (min (α/4) (1/4:ℝ)) pmin ∧
    ordinaryCombinedTriangleEvent d k (P.comap f) (Fconf.comap f) ρi
      (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH cParent Bparent pR pH weight
      j (ordinaryRawRestrictPair f g raw) ∧
    OrdinaryTriangleReferenceNormalizedCuts (P.comap f) (Fconf.comap f) ρi d j δref href
      (ordinaryRawRestrictPair f g raw) (fun e=>coins (Sym2.map f e)) ∧
    OrdinaryDeepCoverLevelInputs 2 (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
      (P.comap f) (Fconf.comap f) ρi (markedVortexInnerHubs Q i) pR pH
      (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity (Fin q) D) β ∧
    ∀Cyc,cParent/(Fintype.card (markedVortexVertexType Q i):ℝ)^(3-2)≤weight Cyc ∧
      weight Cyc≤Bparent/(Fintype.card (markedVortexVertexType Q i):ℝ)^(3-2)
end Oberwolfach
