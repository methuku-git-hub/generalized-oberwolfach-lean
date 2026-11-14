module

public import Oberwolfach.OrdinaryDeepRowsCutsAfterSpacing

@[expose] public section
/-! Name the all-level conclusion together with the prior event on the same
expanded sample and reference-coin outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryDeepRowsCutsAttachedEvent
    (n qCount D mv m K d:ℕ) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin qCount) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH:ℝ)
    (density tR tH:ℕ→ℝ) (s:Fin qCount→Bool→ℝ) (j:Bool)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)]
    (μ:FiniteLaw (∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e))
    (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
    (loss χinner χdeep χone χtwo χcut:ℝ):Prop :=
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ,
    (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH
      (2*pH*(markedVortexInnerHubs Q i).card/(2*p)) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom) ∧
    let νcoins:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin)
    let Inner:=OrdinaryUniformInnerHubEvent m P D mv d β ε Q π hπ (2*p) pH
      (eParent*ε) (hParent*ε) c (4*C/pmin^(3*m+1)) ηHub cap density tR tH s j
    let Deep:=OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρdeep θdeep P D mv β ε Q π hπ j;
    1-(loss+χinner+χdeep+χone+χtwo+χcut)≤((μ.sigma ν).prod νcoins).probability
      (fun z=>((((E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        Deep (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D mv β ε Q π hπ (2*p) pH s j
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D mv β ε Q π hπ (2*p) pH s j
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        ∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
          (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pmin)
end Oberwolfach
