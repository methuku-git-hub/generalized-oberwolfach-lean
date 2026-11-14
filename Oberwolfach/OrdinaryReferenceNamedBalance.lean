module

public import Oberwolfach.OrdinaryAssignedReferenceBalanceColumnsSmall

@[expose] public section
/-! The reference balance and spoke-column event as a named predicate, so
that it can be joined to other same-sample events without a large expression. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryReferenceBalanceColumnsEvent
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Fbad:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ) (rsv σ LF:ℝ)
    (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e):Prop :=
    (∀v,|(((rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (ω e)))\Fbad).degree v:ℝ)-
      2*((Finset.univ.filter (fun w=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (ω e)) false v w)).card:ℝ)|≤σ*n+2*(σ*n)+LF) ∧
    (∀w,|((Finset.univ.filter (fun v=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (ω e)) false v w)).card:ℝ)-rsv*n|<σ*n)
end Oberwolfach
