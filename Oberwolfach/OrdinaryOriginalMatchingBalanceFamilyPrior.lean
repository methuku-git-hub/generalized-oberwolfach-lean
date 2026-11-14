module

public import Oberwolfach.OrdinaryOriginalThresholdFamilyOccupancyShape

@[expose] public section
/-! The explicit event produced by the original-threshold selector, with the
same coherent matching family retained for every permitted deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryOriginalMatchingBalanceFamilyPrior {n qCount K:ℕ}
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (F:Fin qCount → SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K)
    (rsv θ lamMatch aRow γrow p smin σbal aEvent ζDel lamList bMatch:ℝ)
    (q:Fin qCount → Bool → ℝ) (s:Fin qCount → Bool → ℝ)
    {R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e) → Type}
    (E:(Σσ,R σ) → Prop)
    (Core:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e) → Prop)
    (z:Σσ,R σ):Prop :=
  ((((E z ∧ OrdinaryRecodedMatchingExtra P π d θ ((m:ℝ)+1) q s aEvent ζDel lamList Core z.1) ∧
    OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σbal (2*((3*d:ℕ):ℝ)) z.1) ∧
    OrdinaryBoundaryStartEvent π d z.1) ∧ OrdinaryReservedCompletionTests P π d p smin s z.1) ∧
  ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ) ≤ bMatch*n) → 
  ∀(Inner:Finset (Fin n)) (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret),
    OrdinarySelectedMatchingFamilyLocalOccupancyResult F hF Cres i₀ rsv θ lamMatch aRow γrow m d π P Del Inner z.1 tret Jret
end Oberwolfach
