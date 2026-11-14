module

public import Oberwolfach.OrdinaryExpandedVortexTriangleParentSelectionCommon

@[expose] public section
/-! A named product-sample event retaining its prior and all selected parent
and reference-direction tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleParentProductEvent
    (n qCount D mv k d L:ℕ) (hd:2≤d) (β ε α pstar βP ηP ηH βH c B δref href:ℝ)
    (P:SimpleGraph (Fin n)) (Q:Vortex (Fin qCount) P D β ε mv)
    (π:Equiv.Perm (Fin n)) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (weight:∀i,OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q i).toEmbedding) 3→ℝ)
    (p pH:ℝ) (s:Fin qCount→Bool→ℝ) (j:Bool)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)]
    (Good:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop):
    ((Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool))→Prop :=
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
    let g:=fun i=>markedVortexHubEmbedding Q i
    let ρi:=markedVortexPermutation Q π hπ
    let Fconf:=permutationConflictGraph π (3*d)
    let Host:RawWheelOutcome (Fin n) (Fin qCount) Bool Bool→Prop:=fun raw=>∀i≤L,
      ordinaryCombinedTriangleEvent d k (P.comap (f i)) (Fconf.comap (f i)) (ρi i)
        (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B (2*p) pH (weight i)
        j (ordinaryRawRestrictPair (f i) (g i) raw)
    let Cuts:RawWheelOutcome (Fin n) (Fin qCount) Bool Bool×(Sym2 (Fin n)→Bool)→Prop:=fun z=>∀i≤L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (Fconf.comap (f i)) (ρi i) d j δref href
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e));
    fun z=>Good z ∧ Host (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
      Cuts ((fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)),z.2)
end Oberwolfach
