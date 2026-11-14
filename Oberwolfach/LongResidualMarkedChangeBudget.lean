module

public import Oberwolfach.LongMarkedResidualIncomingChange
public import Oberwolfach.LongPreparationIneligibleGraph
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_residual_marked_incoming_change_budget
    {n d:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (M:Fin n→Fin n→ℕ) (Del Small Loss:SimpleGraph (Fin n))
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hsmall:∀x y,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x y=1→Small.Adj x y→Loss.Adj x y)
    (δDel δLoss:ℝ) (hDel:∀v,(Del.degree v:ℝ)≤δDel*n) (hLoss:∀v,(Loss.degree v:ℝ)≤δLoss*n):
    let Bad:=longPreparationIneligibleGraph G π d
    let P:=longResidualHostArc M Small Bad
    let T₁:=longResidualInitialMarked G (fun e=>ω (Sum.inl e)) M Small Bad
    ∀v,((changed (markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v)
      (markedCandidateIncomingTails P T₁ v)).card:ℝ)≤(δDel+δLoss)*n+(6*d+2:ℕ):=by
  intro Bad P T₁ v
  have hc:=long_residual_marked_incoming_change_bound G Del Small Bad Loss ω M hcorrect hsmall v
  have hd₁:=graph_degree_sup_le Del Loss v
  have hd₂:=graph_degree_sup_le (Del⊔Loss) Bad v
  have hi:=long_preparation_ineligible_degree G π d v
  have hDelv:=hDel v
  have hLossv:=hLoss v
  simp only [← SimpleGraph.ncard_neighborSet] at hc hd₁ hd₂ hi hDelv hLossv
  have hr₁:(((Del⊔Loss).neighborSet v).ncard:ℝ)≤
      (Del.neighborSet v).ncard+(Loss.neighborSet v).ncard:=by exact_mod_cast hd₁
  have hr₂:(((Del⊔Loss⊔Bad).neighborSet v).ncard:ℝ)≤
      ((Del⊔Loss).neighborSet v).ncard+(Bad.neighborSet v).ncard:=by exact_mod_cast hd₂
  have hir:((Bad.neighborSet v).ncard:ℝ)≤(6*d+2:ℕ):=by exact_mod_cast hi
  linarith only [hc,hr₁,hr₂,hir,hDelv,hLossv]
end Oberwolfach
