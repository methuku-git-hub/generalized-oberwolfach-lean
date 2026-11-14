module

public import Oberwolfach.LongEveryClassSameDeletionReady
public import Oberwolfach.LongResidualMarkedChangeBudget
public import Oberwolfach.LongApproximateMarkedLoss
public import Oberwolfach.LongMatchingWitnessCorrection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_matching_witness_residual_marked_change_budget
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z T K θ D alpha γ eps βList F hF weight w D₀ C S M Del):
    ∀(Small Loss:SimpleGraph (Fin n)) (δLoss:ℝ),
    Small≤longPhysicalStateGraph G z.1 {2,3}⊔Loss→
    (∀v,(Loss.degree v:ℝ)≤δLoss*n)→
    let Bad:=longPreparationIneligibleGraph G π d
    let P:=longResidualHostArc M Small Bad
    let T₁:=longResidualInitialMarked G (fun e=>z.1 (Sum.inl e)) M Small Bad
    ∀v,((changed (markedRawIncomingTails G (fun e=>z.1 (Sum.inl e)) v)
      (markedCandidateIncomingTails P T₁ v)).card:ℝ)≤(Δ+δLoss)*n+(6*d+2:ℕ):=by
  intro Small Loss δLoss hcover hLoss Bad P T₁
  have hc:=long_matching_witness_correction_bound Δ G π z T θ D alpha γ eps βList F hF weight w D₀ C S Del M hw
  have hs:=long_approximate_embedding_marked_loss G Small Loss z.1 {2,3} (by decide) hcover
  exact long_residual_marked_incoming_change_budget (d:=d) G π z.1 M Del Small Loss hc.1 hs Δ δLoss hc.2 hLoss
end Oberwolfach
