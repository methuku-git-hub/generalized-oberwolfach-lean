module

public import Oberwolfach.OrdinaryTriangleFineRowsCutsProductPrior

@[expose] public section
/-! Name the triangle fine-cover, row and rim-cut event with its prior. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleFineRowsCutsEvent
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U]
    (d:ℕ) (κ aLoad εR εH αcut pmin p pH:ℝ) (P:SimpleGraph V) (D mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε mv) (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (s:U→Color→ℝ) (j:Color)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop)
    (z:(Σσ,R σ)×(Sym2 V→Bool)):Prop :=
      (((E z ∧ OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D mv β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D mv β ε Q π hπ (2*p) pH s j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D mv β ε Q π hπ (2*p) pH s j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      ∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pmin
end Oberwolfach
