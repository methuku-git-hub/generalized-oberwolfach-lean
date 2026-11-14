module

public import Oberwolfach.LongMarkedResidualIncomingChange
public import Oberwolfach.LongApproximateMarkedLoss

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance residualMarkedDeviationDecEq : DecidableEq V := Classical.decEq V

theorem long_residual_marked_deviation_from_sample
    (G Del Small Bad Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hcover:Small≤longPhysicalStateGraph G ω {2,3}⊔Loss)
    (b:ℕ) (err L:ℝ)
    (hraw:∀v,|((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ)-(b:ℝ)|≤err)
    (hLoss:∀v,((Del⊔Loss⊔Bad).degree v:ℝ)≤L):
    let P:=longResidualHostArc M Small Bad
    let T₁:=longResidualInitialMarked G (fun e=>ω (Sum.inl e)) M Small Bad
    ∀v,|(directedInCount P T₁ v:ℝ)-(b:ℝ)|≤err+L:=by
  intro P T₁
  have hs:=long_approximate_embedding_marked_loss G Small Loss ω {2,3} (by decide) hcover
  have hc:=long_residual_marked_incoming_change_bound G Del Small Bad Loss ω M hcorrect hs
  have hchange:∀v,((changed (markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v)
      (markedCandidateIncomingTails P T₁ v)).card:ℝ)≤L:=by
    intro v
    exact (hc v).trans (hLoss v)
  exact marked_candidate_indegree_deviation_from_raw G (fun e=>ω (Sum.inl e)) P T₁ b err L hraw hchange
end Oberwolfach
