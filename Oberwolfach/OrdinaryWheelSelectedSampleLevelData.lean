module

public import Oberwolfach.OrdinaryDeepParentUniformSampleInputs

@[expose] public section
/-! Sample-derived parent, row, cover and weight inputs at a single actual
vortex level, with the shared parent event rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryWheelSelectedSampleLevelData
    (n qCount D mv m K k d:ℕ) (hm:3≤m) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin qCount) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (α ρ₀ pstar βP ηP row ηH βH cParent Bparent εTri δref href:ℝ)
    (pR pH pmin αcut c C ηHub a aLoad ρdeep θdeep cap eParent hParent εR εH:ℝ)
    (density tR tH:ℕ→ℝ) (s:Fin qCount→Bool→ℝ) (j:Bool)
    (raw:RawWheelOutcome (Fin n) (Fin qCount) Bool Bool) (coins:Sym2 (Fin n)→Bool) (i:ℕ)
    (weight:OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q i)) (m+1)→ℝ):Prop :=
    let Fconf:=permutationConflictGraph π (3*d)
    let f:=(markedVortexVertexEmbedding Q i).toEmbedding
    let g:=markedVortexHubEmbedding Q i
    let ρi:=markedVortexPermutation Q π hπ i;
    OrdinaryUniformInnerHubEvent m P D mv d β ε Q π hπ pR pH (eParent*ε) (hParent*ε)
      c (4*C/pmin^(3*m+1)) ηHub cap density tR tH s j raw ∧
    OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρdeep θdeep P D mv β ε Q π hπ j raw ∧
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ pR pH s j raw ∧
    OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ pR pH s j raw ∧
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1)) (sampledOrientation (rawWheelGraph P raw) coins) αcut pmin ∧
    ordinaryCombinedHostEvent m d k hm (P.comap f) (Fconf.comap f) ρi
      (max (1/2) (cycleThreshold (m+1))) α pstar βP ηP row ηH βH cParent Bparent pR pH weight
      (fun u=>s (g u)) j (ordinaryRawRestrictPair f g raw) ∧
    OrdinaryTriangleReferenceNormalizedCuts (P.comap f) (Fconf.comap f) ρi d j δref href
      (ordinaryRawRestrictPair f g raw) (fun e=>coins (Sym2.map f e)) ∧
    OrdinaryDeepCoverLevelInputs m (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
      (P.comap f) (Fconf.comap f) ρi (markedVortexInnerHubs Q i) pR pH
      (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity (Fin qCount) D) β ∧
    ∀Cyc,cParent/(Fintype.card (markedVortexVertexType Q i):ℝ)^((m+1)-2)≤weight Cyc ∧
      weight Cyc≤Bparent/(Fintype.card (markedVortexVertexType Q i):ℝ)^((m+1)-2)
end Oberwolfach
